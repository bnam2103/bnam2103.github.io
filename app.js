/* =========================
   SESSION — VERA vs BMO (separate conversation memory on the server)
========================= */

const VERA_SESSION_STORAGE_KEY = "vera_session_id";
const BMO_SESSION_STORAGE_KEY = "bmo_session_id";

/**
 * Session ids are tab-scoped: switching pages keeps them, closing the tab clears them.
 * Migrate legacy ids from localStorage once for backward compatibility.
 */
function getSessionScopedId(key) {
  let id = "";
  try {
    id = sessionStorage.getItem(key) || "";
  } catch (_) {}
  if (id) return id;
  try {
    const legacy = localStorage.getItem(key) || "";
    if (legacy) {
      sessionStorage.setItem(key, legacy);
      localStorage.removeItem(key);
      return legacy;
    }
  } catch (_) {}
  return "";
}

function setSessionScopedId(key, id) {
  try {
    sessionStorage.setItem(key, id);
  } catch (_) {}
  try {
    localStorage.removeItem(key);
  } catch (_) {}
}

function getSessionId() {
  const bmo = document.body.classList.contains("bmo-open");
  const key = bmo ? BMO_SESSION_STORAGE_KEY : VERA_SESSION_STORAGE_KEY;
  let id = getSessionScopedId(key);
  if (!id) {
    id = crypto.randomUUID();
    setSessionScopedId(key, id);
  }
  return id;
}

/**
 * Call when opening BMO: new backend session, empty log, voice input default, clear side panel.
 * Exposed for index.html `openBmoPage`.
 */
function resetBmoSessionAndUi() {
  const newId = crypto.randomUUID();
  setSessionScopedId(BMO_SESSION_STORAGE_KEY, newId);

  const convo = document.getElementById("bmo-conversation");
  if (convo) convo.replaceChildren();

  const textIn = document.getElementById("bmo-text-input");
  if (textIn) textIn.value = "";

  const voiceBar = document.getElementById("bmo-voice-bar");
  const keyboardBar = document.getElementById("bmo-keyboard-bar");
  const toggleBtn = document.getElementById("bmo-input-toggle");
  if (voiceBar) voiceBar.classList.remove("hidden");
  if (keyboardBar) keyboardBar.classList.add("hidden");
  if (toggleBtn) toggleBtn.textContent = "⌨️";

  const bmoAudio = document.getElementById("bmo-audio");
  if (bmoAudio) {
    bmoAudio.pause();
    bmoAudio.removeAttribute("src");
    bmoAudio.load?.();
  }

  document.getElementById("bmo-page")?.classList.remove("bmo-tts-mouth");
  document.getElementById("bmo-smile-svg")?.removeAttribute("data-bmo-tts-emotion");

  hideSidePanel();
}

/**
 * Call when (re)entering the VERA app: new backend session, empty log, voice UI default, clear side panel.
 * Used on boot/reveal and when returning from BMO via the VERA nav control.
 */
function resetVeraSessionAndUi() {
  const prevSessionId = getSessionScopedId(VERA_SESSION_STORAGE_KEY);
  const newId = crypto.randomUUID();
  setSessionScopedId(VERA_SESSION_STORAGE_KEY, newId);

  const convo = document.getElementById("vera-conversation");
  if (convo) convo.replaceChildren();

  const textIn = document.getElementById("vera-text-input");
  if (textIn) textIn.value = "";

  const voiceBar = document.getElementById("vera-voice-bar");
  const keyboardBar = document.getElementById("vera-keyboard-bar");
  const toggleBtn = document.getElementById("vera-input-toggle");
  if (voiceBar) voiceBar.classList.remove("hidden");
  if (keyboardBar) keyboardBar.classList.add("hidden");
  if (toggleBtn) toggleBtn.textContent = "⌨️";

  const veraAudio = document.getElementById("vera-audio");
  if (veraAudio) {
    veraAudio.pause();
    veraAudio.removeAttribute("src");
    veraAudio.load?.();
  }

  /* Reset work-mode client artifacts too: checklist + reasoning panes/state. */
  try {
    localStorage.removeItem(WORK_CHECKLIST_STORAGE_KEY);
    localStorage.removeItem(WORK_CHECKLIST_COMPLETED_COLLAPSED_KEY);
    if (prevSessionId) {
      localStorage.removeItem(`${REASONING_TABS_STATE_STORAGE_KEY_PREFIX}:${prevSessionId}`);
    }
  } catch (_) {}
  ensureFixedReasoningLanePanels(new Map(), 0);
  renderReasoningTabStrip();
  loadWorkChecklistItems();
  flashWorkChecklistPlanHint("");
  workModeReasoningConfirmPending = null;
  workModeReasoningAttachment = null;
  for (const ctl of workModeReasoningAbortControllers.values()) {
    try {
      ctl.abort();
    } catch (_) {}
  }
  workModeReasoningAbortControllers.clear();
  workModeReasoningLaneWaitQueue.length = 0;
  workModeTypedTurnQueue.length = 0;
  workModeTypedQueueDraining = false;
  WORK_MODE_REASONING_LANES.forEach((lane) => workModeReasoningLaneBusy.set(lane.idx, false));
  syncWorkModeReasoningCancelButton();
  setWorkModeAttachmentMeta("");

  hideSidePanel();
}

window.resetBmoSessionAndUi = resetBmoSessionAndUi;
window.resetVeraSessionAndUi = resetVeraSessionAndUi;
window.persistVeraChatState = persistVeraChatState;

/* =========================
   GLOBAL STATE
========================= */

let micStream = null;
let audioCtx = null;
let analyser = null;
let mediaRecorder = null;

let interruptRecorder = null;
let interruptChunks = [];
let interruptRecording = false;

let audioChunks = [];
let hasSpoken = false;
let lastVoiceTime = 0;

let listening = false;
let processing = false;
let rafId = null;
/** `startListening` no-speech watchdog; must be cleared when switching to PTT or the new recorder gets stopped. */
let speechWaitTimeoutId = null;
let interruptSpeechFrames = 0;
let interruptSpeechStart = 0;
/** Ms of speechLike time accumulated from RAF deltas (gaps do not add). */
let interruptSpeechAccumMs = 0;
let lastInterruptDetectTime = 0;
let interruptLastSpeechLikeTime = 0;
/** Snapshot from detectInterrupt when interruptSpeech() fires (for server interrupt_debug). */
let lastInterruptProbe = null;
/** Last frame where speechLike was true (same as trigger frame when interrupt fires). */
let lastInterruptSpeechLikeSnapshot = null;
/** Throttled VAD samples for mobile interrupt debug panel. */
let lastMobileVadSampleLogAt = 0;
const MOBILE_VAD_SAMPLE_INTERVAL_MS = 220;
const INTERRUPT_VAD_LOG_MAX = 200;
let interruptVadLogLines = [];
let pttRecording = false;
let inputMuted = false;
let suppressNextUtterance = false;

/** Web Speech API (main + interrupt + post-interrupt); mutually exclusive instances. */
let mainBrowserRecognition = null;
let mainBrowserSilenceTimer = null;
let mainBrowserFinalTranscript = "";
/** @type {HTMLElement | null} */
let mainBrowserLiveBubble = null;
/** Translucent live preview during TTS interrupt detection (browser ASR); promoted to main live bubble on interrupt. */
/** @type {HTMLElement | null} */
let interruptDetectionBubbleEl = null;

let interruptDetectRecognition = null;
let interruptBrowserDetectActive = false;
let postInterruptRecognition = null;
let interruptPartialAccumMs = 0;
let interruptPartialLastChangeAt = 0;
let interruptPartialLastText = "";
let interruptPartialRafTime = 0;
/** "main" continuous/PTT vs "interrupt" post-barge-in utterance — controls silence-timer finalize. */
let mainBrowserFinalizeKind = "main";
let mainBrowserLastInterim = "";
/** After >2 words during TTS, barge-in latched: same SR stream continues until 1.3s silence → LLM (no second SR). */
let interruptBargeInLatched = false;
/** If interrupt-detect SR never emits onresult while TTS plays, abort so heuristic fallback can run. */
let interruptDetectNoResultWatchdogTimer = null;

/** Debounce main SR onend → startListening recovery (Chrome sometimes ends the session with no error). */
let browserAsrMainEndRecoveryTimer = null;
/** Debounce tab focus/visibility → resume main SR when Chrome ended the session in background. */
let browserAsrVisibilityResumeTimer = null;

/** Opt-in via localStorage VERA_DEBUG_BROWSER_ASR_STUCK=1 — heartbeats + onend/onerror/silence-timer traces. */
let browserAsrStuckWatchdogId = null;
let browserAsrSessionStartedAt = 0;
let browserAsrLastResultAt = 0;
let browserAsrHadAnyResult = false;
let browserAsrLastResultRole = "";

let audioStartedAt = 0;
let voiceUxTurn = null;
let textUxTurn = null;
// let interruptStart = 0;
let listeningMode = "continuous"; 
let waveState = "idle";   
let waveEnergy = 0;     

let requestInFlight = false; // 🔑 NEW

/** Start of a voice UX turn: t0 for perceived latency (end of user speech in the browser). */
function beginVoiceUxTurn() {
  voiceUxTurn = {
    speechEndAt: performance.now(),
    firstAudioLogged: false,
    mainReplyLogged: false
  };
}

/** First *any* audio in this turn (typically main `(main-reply)`). */
function logVoiceFirstAudio(kind) {
  if (!voiceUxTurn || voiceUxTurn.firstAudioLogged) return;
  const elapsedMs = performance.now() - voiceUxTurn.speechEndAt;
  voiceUxTurn.firstAudioLogged = true;
  console.log(`[UX][VOICE] SpeechEnd→FirstAudio=${(elapsedMs / 1000).toFixed(3)}s (${kind})`);
}

/**
 * Primary perceived voice metric: end of user speech → first main reply TTS playback.
 * (Not server `latency.total_s`, not `[UX][PIPE]` — those are diagnostics only.)
 */
function logVoiceMainReplyAudio() {
  if (!voiceUxTurn || voiceUxTurn.mainReplyLogged) return;
  const elapsedMs = performance.now() - voiceUxTurn.speechEndAt;
  voiceUxTurn.mainReplyLogged = true;
  console.log(`[UX][VOICE] SpeechEnd→MainReplyAudio=${(elapsedMs / 1000).toFixed(3)}s`);
}

/** Debug: seconds from speech end — use to see upload vs TTFB vs first chunk vs decode (server TOTAL is a different clock). */
function logVoicePipe(label) {
  if (!voiceUxTurn?.speechEndAt) return;
  const s = ((performance.now() - voiceUxTurn.speechEndAt) / 1000).toFixed(3);
  console.log(`[UX][VOICE][PIPE] ${label}  +${s}s from SpeechEnd`);
}

/** Set localStorage VERA_DEBUG_TRANSCRIPTS to "0" to silence [VOICE][TRANSCRIPT] logs. */
function voiceTranscriptDebugEnabled() {
  try {
    return localStorage.getItem("VERA_DEBUG_TRANSCRIPTS") !== "0";
  } catch {
    return true;
  }
}

/** Set localStorage VERA_DEBUG_PARTIAL_ASR_DONE to "0" to silence [VOICE][PARTIAL-ASR] done / segment logs. */
function voicePartialAsrDoneLogEnabled() {
  try {
    return localStorage.getItem("VERA_DEBUG_PARTIAL_ASR_DONE") !== "0";
  } catch {
    return true;
  }
}

/**
 * Verbose browser-ASR diagnostics (heartbeats, onerror, silence-timer skips). Enable with:
 *   localStorage.setItem("VERA_DEBUG_BROWSER_ASR_STUCK", "1")
 * Reload the page after setting. (Recovery from dead SR and zero-audio TTS do not require this.)
 */
function browserAsrStuckDebugEnabled() {
  try {
    return localStorage.getItem("VERA_DEBUG_BROWSER_ASR_STUCK") === "1";
  } catch {
    return false;
  }
}

function stopBrowserAsrStuckWatchdog() {
  if (browserAsrStuckWatchdogId != null) {
    clearInterval(browserAsrStuckWatchdogId);
    browserAsrStuckWatchdogId = null;
  }
}

function snapshotBrowserAsrDebugState() {
  const now = performance.now();
  const sinceSessionStart = browserAsrSessionStartedAt
    ? Math.round(now - browserAsrSessionStartedAt)
    : null;
  const sinceLastResult =
    browserAsrHadAnyResult && browserAsrLastResultAt
      ? Math.round(now - browserAsrLastResultAt)
      : null;
  return {
    listening,
    processing,
    requestInFlight,
    waveState,
    interruptBrowserDetectActive,
    interruptBargeInLatched,
    mainBrowserFinalizeKind,
    hasMainRecognizer: !!mainBrowserRecognition,
    hasInterruptRecognizer: !!interruptDetectRecognition,
    hasPostInterruptRecognizer: !!postInterruptRecognition,
    silenceTimerActive: mainBrowserSilenceTimer != null,
    speechWaitPending: speechWaitTimeoutId != null,
    sinceSessionStartMs: sinceSessionStart,
    sinceLastResultMs: sinceLastResult,
    hadAnyResult: browserAsrHadAnyResult,
    lastResultRole: browserAsrLastResultRole || null,
    transcriptPreview: ((mainBrowserFinalTranscript + mainBrowserLastInterim).trim()).slice(0, 120),
  };
}

function logBrowserAsrStuckEvent(message, extra = {}) {
  if (!browserAsrStuckDebugEnabled()) return;
  console.log("[VOICE][BROWSER-ASR-STUCK]", message, { ...extra, ...snapshotBrowserAsrDebugState() });
}

function markBrowserAsrResult(role) {
  browserAsrLastResultAt = performance.now();
  browserAsrHadAnyResult = true;
  browserAsrLastResultRole = role;
}

/**
 * Call after a SpeechRecognition `.start()` succeeds. Heartbeats every 5s; warns if no `onresult` for 8s+ after
 * at least one result, or 12s+ with zero results (Chrome sometimes stops emitting).
 */
function beginBrowserAsrStuckSession(activeRole) {
  if (!browserAsrStuckDebugEnabled()) return;
  browserAsrSessionStartedAt = performance.now();
  browserAsrLastResultAt = 0;
  browserAsrHadAnyResult = false;
  browserAsrLastResultRole = activeRole;
  stopBrowserAsrStuckWatchdog();
  browserAsrStuckWatchdogId = window.setInterval(() => {
    if (!browserAsrStuckDebugEnabled()) {
      stopBrowserAsrStuckWatchdog();
      return;
    }
    const snap = snapshotBrowserAsrDebugState();
    const anyRec =
      snap.hasMainRecognizer || snap.hasInterruptRecognizer || snap.hasPostInterruptRecognizer;
    if (!anyRec) {
      stopBrowserAsrStuckWatchdog();
      return;
    }
    console.log("[VOICE][BROWSER-ASR-STUCK] heartbeat", snap);
    if (snap.hadAnyResult && snap.sinceLastResultMs != null && snap.sinceLastResultMs > 8000) {
      console.warn(
        "[VOICE][BROWSER-ASR-STUCK] no onresult for 8s+ while recognizer still referenced",
        snap
      );
    }
    if (!snap.hadAnyResult && snap.sinceSessionStartMs != null && snap.sinceSessionStartMs > 12000) {
      console.warn("[VOICE][BROWSER-ASR-STUCK] no onresult since session start (12s+)", snap);
    }
  }, 5000);
  logBrowserAsrStuckEvent("session_started", { activeRole });
}

/** One browser-ASR utterance finished (silence gate) and will go to Thinking/infer. */
function logPartialAsrUtteranceDone(text, meta = {}) {
  if (!voicePartialAsrDoneLogEnabled()) return;
  console.log("[VOICE][PARTIAL-ASR] done", { text: text ?? "", ...meta });
}

/** Chrome emitted a final segment for this result (may be multiple per spoken phrase). */
function logPartialAsrSegmentFinal(segmentText, meta = {}) {
  if (!voicePartialAsrDoneLogEnabled()) return;
  console.log("[VOICE][PARTIAL-ASR] segment-final", {
    segment: segmentText ?? "",
    ...meta
  });
}

/**
 * @param {"final"} phase — committed user line (bubble) from `/infer`.
 * @param {Record<string, unknown>} [meta] — e.g. { path: "main-ndjson" }
 */
function logVoiceTranscript(phase, text, meta = {}) {
  if (!voiceTranscriptDebugEnabled()) return;
  console.log("[VOICE][TRANSCRIPT]", { phase, ...meta, text: text ?? "" });
}

function logFinalTranscriptSentToLlm(path, text) {
  if (!voiceTranscriptDebugEnabled()) return;
  console.log("[VOICE][LLM-INPUT]", { path, text: text ?? "" });
}

function beginTextUxTurn() {
  textUxTurn = {
    sendAt: performance.now(),
    firstAudioLogged: false,
    mainReplyLogged: false
  };
}

function logTextFirstAudio(kind) {
  if (!textUxTurn || textUxTurn.firstAudioLogged) return;
  const elapsedMs = performance.now() - textUxTurn.sendAt;
  textUxTurn.firstAudioLogged = true;
  console.log(`[UX][TEXT] Send→FirstAudio=${(elapsedMs / 1000).toFixed(3)}s (${kind})`);
}

function logTextMainReplyAudio() {
  if (!textUxTurn || textUxTurn.mainReplyLogged) return;
  const elapsedMs = performance.now() - textUxTurn.sendAt;
  textUxTurn.mainReplyLogged = true;
  console.log(`[UX][TEXT] Send→MainReplyAudio=${(elapsedMs / 1000).toFixed(3)}s`);
}

/** Server-side breakdown + optional client TTFB split — for attribution, not end-user perceived time (see SpeechEnd→MainReplyAudio). */
function logInferLatency(data, label, clientTtfbMs) {
  const L = data?.latency;
  if (!L || typeof L !== "object") return;
  const parts = [];
  if (L.short_circuit) parts.push(`short_circuit=${L.short_circuit}`);
  if (L.pre_asr_s != null) parts.push(`PreASR=${L.pre_asr_s}s`);
  if (L.asr_lock_s != null) parts.push(`ASR_lock=${L.asr_lock_s}s`);
  if (L.asr_transcribe_s != null) parts.push(`ASR_transcribe=${L.asr_transcribe_s}s`);
  if (L.bridge_s != null) parts.push(`Bridge=${L.bridge_s}s`);
  if (L.llm_s != null) parts.push(`LLM=${L.llm_s}s`);
  if (L.llm_first_token_s != null) parts.push(`LLM_first_token=${L.llm_first_token_s}s`);
  if (L.llm_first_sentence_ready_s != null)
    parts.push(`LLM_first_sentence_ready=${L.llm_first_sentence_ready_s}s`);
  if (L.post_llm_s != null) parts.push(`PostLLM=${L.post_llm_s}s`);
  if (L.tts_s != null) parts.push(`TTS=${L.tts_s}s`);
  if (L.tts_first_chunk_s != null) parts.push(`TTS_first_chunk=${L.tts_first_chunk_s}s`);
  if (L.first_tts_audio_ready_total_s != null)
    parts.push(`first_TTS_file_ready_total=${L.first_tts_audio_ready_total_s}s`);
  if (L.first_tts_audio_ready_after_pre_asr_s != null)
    parts.push(`first_TTS_file_ready_after_PreASR=${L.first_tts_audio_ready_after_pre_asr_s}s`);
  if (L.first_tts_audio_ready_after_asr_end_s != null)
    parts.push(`first_TTS_file_ready_after_ASR_end=${L.first_tts_audio_ready_after_asr_end_s}s`);
  if (L.total_s != null) parts.push(`TOTAL=${L.total_s}s`);
  if (L.sum_segments_s != null) parts.push(`Σ=${L.sum_segments_s}s`);
  if (L.drift_s != null) parts.push(`drift=${L.drift_s}s`);
  if (L.llm_internal_reported_s != null) parts.push(`llm_internal=${L.llm_internal_reported_s}s`);
  const line = parts.length ? parts.join(" | ") : JSON.stringify(L);
  console.log(`[UX][LATENCY][${label}] ${line}`, L);
  if (L.total_s != null && clientTtfbMs != null && Number.isFinite(clientTtfbMs)) {
    console.log(
      `[UX][LATENCY][split][${label}] backend total_s=${L.total_s} (server clock: infer start→end of full NDJSON stream on Python) | ` +
        `client_ttfb_ms=${Math.round(clientTtfbMs)} (browser: fetch() start→first response headers; includes body upload + Worker/proxy + network + server until it can stream)`
    );
    console.log(
      `[UX][LATENCY][hint] Backend work = ASR / LLM / TTS columns above (Python). ` +
        `Upload/proxy/internet vs backend: compare client_ttfb_ms to how “heavy” those segments are; TOTAL is not the same moment as TTFB (TOTAL waits for the whole stream to finish on the server).`
    );
  }
}

/* =========================
   CONFIG
========================= */

const IS_MOBILE = window.matchMedia("(max-width: 768px)").matches;

function hasMobileVadLogQuery() {
  try {
    return new URLSearchParams(window.location.search).get("vadlog") === "1";
  } catch {
    return false;
  }
}

/** Mobile viewport + `?vadlog=1` — inject VAD/interrupt debug UI and capture log lines. */
const MOBILE_VAD_DEBUG = IS_MOBILE && hasMobileVadLogQuery();

const VOLUME_THRESHOLD = 0.0078; // slightly lower so quieter speech starts more reliably
const SILENCE_MS = 950;     // silence before ending speech
const TRAILING_MS = 300;   // guaranteed tail
/**
 * Browser SpeechRecognition: cap before first partial (`hasSpoken` false). 0 = off (desktop Chrome can be slow).
 */
const MAX_WAIT_FOR_BROWSER_ASR_INITIAL_MS = 0;
/**
 * MediaRecorder + VAD fallback (non–secure pages, iOS Safari without Web Speech, etc.): if VAD never marks
 * speech, stop the recorder so we do not spin "Listening…" forever. Does not apply to browser ASR.
 */
const MAX_WAIT_FOR_MEDIA_RECORDER_INITIAL_MS = 60000;
const MIN_AUDIO_BYTES = 1500;
const INTERRUPT_MIN_FRAMES = 1;

/**
 * End-of-utterance (continuous listen + interrupt capture): a frame only resets the
 * silence timer if RMS and ZCR both look like voiced speech. Room tone / fan / AC often
 * stays above VOLUME_THRESHOLD but has ZCR outside this band, so the clip can still end
 * after SILENCE_MS once the user stops talking.
 */
const LISTEN_END_ZCR_MIN = 0.022;
const LISTEN_END_ZCR_MAX = 0.19;

/* Interrupt while TTS plays: RMS / ZCR / crest heuristics + sustain/gap timing (no WASM VAD). */
/* Voiced-speech band for ZCR (zero-crossings / sample). Outside this → rustle/AC/fan/clicks. */
const INTERRUPT_ZCR_MIN = 0.028;
const INTERRUPT_ZCR_MAX = 0.165;
const MAX_SPEECH_RMS = 0.078;
const INTERRUPT_RMS = 0.0105;
/**
 * Min accumulated ms where speechLike is true (wall-clock gaps and quiet frames do not count).
 * Interrupt fires only on a speechLike frame after this threshold.
 * Phone viewports use a shorter window for faster interrupt.
 */
const INTERRUPT_SUSTAIN_MS_DESKTOP = 350;
const INTERRUPT_SUSTAIN_MS_PHONE = 100;

function getInterruptSustainMs() {
  return isNarrowViewport()
    ? INTERRUPT_SUSTAIN_MS_PHONE
    : INTERRUPT_SUSTAIN_MS_DESKTOP;
}

/** Max ms without a speech-like frame before resetting the sustain counter. */
const INTERRUPT_GAP_RESET_MS = 110;
/** peak/RMS; impulsive handling noise is often very spiky vs sustained vowels. */
const INTERRUPT_MAX_CREST = 38;
const API_URL = "https://vera-api.vera-api-ned.workers.dev";

/** Request NDJSON streaming TTS from /infer and /text so the first /audio URL arrives as soon as it is synthesized. */
const DEFAULT_STREAM_TTS = true;

/** Browser Web Speech API: live partials, then 1.3s stable transcript → /infer without server ASR. */
let browserAsrMainSilenceMs = 1300;
/** Main browser-ASR only: minimum visible chars before showing partial bubble. */
let mainAsrPartialMinChars = 10;
/** Min accumulated ms of changing partial transcript to count as interrupt (vs VAD on audio). */
let browserAsrInterruptSustainMs = 350;
/** Reset interrupt sustain if no transcript change for this long (ms). */
let browserAsrInterruptGapMs = 120;
/** Fire interrupt when browser partial ASR reaches this many words, or when partial text is stable long enough. */
let interruptBrowserMinWords = 2;

function browserAsrSupported() {
  return typeof (window.SpeechRecognition || window.webkitSpeechRecognition) === "function";
}

/** Match device locale (Chrome/Android works better than a hardcoded en-US for many users). */
function getSpeechRecognitionLang() {
  try {
    const lang = (navigator.languages && navigator.languages[0]) || navigator.language;
    if (lang && typeof lang === "string" && lang.length >= 2) return lang;
  } catch {}
  return "en-US";
}

/** Retries for main SR `network` errors (common on mobile data / brief offline). */
let browserAsrMainNetworkRetries = 0;
const BROWSER_ASR_MAIN_NETWORK_RETRY_MAX = 2;

const VERA_SETTING_ASR_SILENCE_MS_KEY = "vera_setting_asr_silence_ms_v1";
const VERA_SETTING_ASR_MODE_KEY = "vera_setting_asr_mode_v1";
const VERA_SETTING_WORKMODE_MUTE_KEY = "vera_setting_workmode_mute_v1";
const VERA_SETTING_MAIN_ASR_PARTIAL_MIN_CHARS_KEY = "vera_setting_main_asr_partial_min_chars_v1";

function logVeraSettings(event, data = {}) {
  try {
    console.log("[SETTINGS]", event, data);
  } catch (_) {}
}

/**
 * Set true after Web Speech returns not-allowed / service-not-allowed so we stop retrying
 * (retries re-trigger permission prompts, especially on file://).
 */
let browserAsrPermanentlyDisabled = false;

/**
 * Google Chrome (desktop + Android + iOS shell): Web Speech partials are the intended path.
 * Other mobile browsers (Safari, Firefox, Samsung Internet, …) default to MediaRecorder + server ASR.
 *
 * Overrides:
 * - localStorage VERA_BROWSER_ASR = "0" → never use browser ASR (any device).
 * - Narrow viewports (max-width 768px): default to MediaRecorder + server ASR (more reliable than Web Speech on phones).
 * - localStorage VERA_BROWSER_ASR_PHONE = "1" → opt in to Web Speech on narrow viewports (Chrome only).
 * - localStorage VERA_BROWSER_ASR_PHONE = "0" → force server ASR on narrow viewports (same as default).
 */
function isLikelyGoogleChrome() {
  try {
    const ua = navigator.userAgent || "";
    if (/Edg\/|OPR\/|Opera\/|SamsungBrowser/i.test(ua)) return false;
    if (/CriOS\//.test(ua)) return true;
    return /Chrome\/\d/.test(ua) && String(navigator.vendor || "").includes("Google");
  } catch {
    return false;
  }
}

/** Matches browserAsrPreferred() narrow branch: phone-sized layout vs desktop. */
function isNarrowViewport() {
  try {
    return window.matchMedia("(max-width: 768px)").matches;
  } catch {
    return false;
  }
}

function browserAsrPreferred() {
  if (browserAsrPermanentlyDisabled) return false;
  if (getVeraAsrMode() === "single") return false;
  /* Opening index.html as file:// is unstable for Web Speech + permissions; use http://localhost or HTTPS. */
  if (typeof location !== "undefined" && location.protocol === "file:") {
    return false;
  }
  /* Web Speech API requires a secure context (HTTPS or localhost). */
  if (typeof window.isSecureContext !== "undefined" && !window.isSecureContext) {
    return false;
  }
  if (!browserAsrSupported()) return false;
  try {
    if (localStorage.getItem("VERA_BROWSER_ASR") === "0") return false;
  } catch {}
  try {
    if (isNarrowViewport()) {
      try {
        if (localStorage.getItem("VERA_BROWSER_ASR_PHONE") === "0") return false;
      } catch {}
      try {
        if (localStorage.getItem("VERA_BROWSER_ASR_PHONE") === "1") {
          return isLikelyGoogleChrome();
        }
      } catch {}
      return false;
    }
  } catch {}
  return true;
}

function getVeraAsrSilenceMs() {
  try {
    const v = Number(localStorage.getItem(VERA_SETTING_ASR_SILENCE_MS_KEY));
    if (v === 1000 || v === 1300 || v === 1600) return v;
  } catch (_) {}
  return 1300;
}

function setVeraAsrSilenceMs(v) {
  const next = v === 1000 || v === 1300 || v === 1600 ? v : 1300;
  browserAsrMainSilenceMs = next;
  try {
    localStorage.setItem(VERA_SETTING_ASR_SILENCE_MS_KEY, String(next));
  } catch (_) {}
  logVeraSettings("save_silence_ms", { value: next });
}

function getVeraAsrMode() {
  try {
    const v = String(localStorage.getItem(VERA_SETTING_ASR_MODE_KEY) || "").trim();
    if (v === "single" || v === "streaming") return v;
  } catch (_) {}
  return "streaming";
}

function setVeraAsrMode(mode) {
  const next = mode === "single" ? "single" : "streaming";
  try {
    localStorage.setItem(VERA_SETTING_ASR_MODE_KEY, next);
  } catch (_) {}
  logVeraSettings("save_asr_mode", { value: next });
}

function getMainAsrPartialMinChars() {
  try {
    const v = Number(localStorage.getItem(VERA_SETTING_MAIN_ASR_PARTIAL_MIN_CHARS_KEY));
    if (v === 5 || v === 8 || v === 10 || v === 12 || v === 15) return v;
  } catch (_) {}
  return 10;
}

function setMainAsrPartialMinChars(v) {
  const next = v === 5 || v === 8 || v === 10 || v === 12 || v === 15 ? v : 10;
  mainAsrPartialMinChars = next;
  try {
    localStorage.setItem(VERA_SETTING_MAIN_ASR_PARTIAL_MIN_CHARS_KEY, String(next));
  } catch (_) {}
  logVeraSettings("save_main_asr_partial_min_chars", { value: next });
}

function isWorkModeMuteEnabled() {
  try {
    return localStorage.getItem(VERA_SETTING_WORKMODE_MUTE_KEY) === "1";
  } catch (_) {
    return false;
  }
}

function setWorkModeMuteEnabled(on) {
  try {
    localStorage.setItem(VERA_SETTING_WORKMODE_MUTE_KEY, on ? "1" : "0");
  } catch (_) {}
  logVeraSettings("save_workmode_mute", { value: on ? 1 : 0 });
  applyVeraWorkModeMuteSetting();
}

function applyVeraWorkModeMuteSetting() {
  const veraAudio = document.getElementById("vera-audio");
  const inWork = Boolean(document.getElementById("vera-app")?.classList.contains("work-mode"));
  const mute = isWorkModeMuteEnabled() && inWork;
  if (veraAudio instanceof HTMLAudioElement) {
    veraAudio.muted = mute;
  }
  const vg = ttsByMode?.vera?.gain;
  if (vg && audioCtx && typeof vg.gain?.setValueAtTime === "function") {
    try {
      vg.gain.setValueAtTime(mute ? 0 : 1, audioCtx.currentTime);
    } catch (_) {}
  }
  logVeraSettings("apply_workmode_mute", {
    enabled_setting: isWorkModeMuteEnabled() ? 1 : 0,
    in_work_mode: inWork ? 1 : 0,
    effective_mute: mute ? 1 : 0,
    has_gain: vg ? 1 : 0
  });
}

function shouldStreamTts() {
  if (getVeraAsrMode() === "single") return false;
  if (!DEFAULT_STREAM_TTS) return false;
  if (appModePrefix() === "vera" && isVeraWorkModeOn() && isWorkModeMuteEnabled()) {
    logVeraSettings("stream_tts_forced_off_workmode_mute", { value: 0 });
    return false;
  }
  return true;
}

browserAsrMainSilenceMs = getVeraAsrSilenceMs();
mainAsrPartialMinChars = getMainAsrPartialMinChars();

function disableBrowserAsrForSession(reason) {
  browserAsrPermanentlyDisabled = true;
  if (speechWaitTimeoutId != null) {
    clearTimeout(speechWaitTimeoutId);
    speechWaitTimeoutId = null;
  }
  console.warn("[BrowserASR] disabled for this session:", reason);
}

function isFatalBrowserSpeechError(code) {
  return (
    code === "not-allowed" ||
    code === "service-not-allowed" ||
    code === "audio-capture"
  );
}

function isNdjsonTtsResponse(res) {
  const ct = res.headers.get("content-type") || "";
  return ct.includes("ndjson") || ct.includes("x-ndjson");
}

/* =========================
   DOM — VERA vs BMO (prefix ids: vera-* / bmo-*)
========================= */

function appModePrefix() {
  return document.body.classList.contains("bmo-open") ? "bmo" : "vera";
}

function uiEl(suffix) {
  return document.getElementById(`${appModePrefix()}-${suffix}`);
}

function getAudioEl() {
  return document.getElementById(`${appModePrefix()}-audio`);
}

function getWaveCanvas() {
  return document.getElementById(`${appModePrefix()}-waveform`);
}

function getWaveCtx() {
  const c = getWaveCanvas();
  return c ? c.getContext("2d") : null;
}

const ttsByMode = {
  vera: { source: null, analyser: null, gain: null },
  bmo: { source: null, analyser: null, gain: null }
};

function getTtsAnalyser() {
  return ttsByMode[appModePrefix()]?.analyser ?? null;
}

["vera-audio", "bmo-audio"].forEach((id) => {
  const a = document.getElementById(id);
  if (a) a.crossOrigin = "anonymous";
});

let waveformData = null;
let frequencyData = null;    // Uint8Array for spectrum
let smoothedBars = null;     // smooth bar heights over time
let rippleRings = [];        // { radius, opacity } for ripple effect
let lastRippleTime = 0;
const RIPPLE_SPAWN_INTERVAL_MS = 120;
let waveformRaf = null;

function resizeWaveCanvas() {
  const canvas = getWaveCanvas();
  const waveCtx = getWaveCtx();
  if (!canvas || !waveCtx) return;

  const dpr = window.devicePixelRatio || 1;
  const rect = canvas.getBoundingClientRect();
  /* Hidden / not laid out yet: don't shrink buffer to 0 (avoids blurry upscale when shown). */
  if (rect.width < 4 || rect.height < 4) return;

  canvas.width = rect.width * dpr;
  canvas.height = rect.height * dpr;

  waveCtx.setTransform(1, 0, 0, 1, 0, 0);
  waveCtx.scale(dpr, dpr);
}

window.addEventListener("load", () => {
  resizeWaveCanvas();
});

window.addEventListener("resize", resizeWaveCanvas);

const serverStatusEl = document.getElementById("server-status");

const feedbackInput = document.getElementById("feedback-input");
const sendFeedbackBtn = document.getElementById("send-feedback");
const feedbackStatusEl = document.getElementById("feedback-status");

/* =========================
   SERVER HEALTH
========================= */

async function checkServer() {
  let state = "offline";

  try {
    // 🔥 NEW — check full server state
    const statusRes = await fetch(`${API_URL}/status`, {
      cache: "no-store"
    });

    if (statusRes.ok) {
      const data = await statusRes.json();
      state = data.state; // "ready" or "starting"
    } else {
      state = "offline";
    }
  } catch {
    state = "offline";
  }

  // =========================
  // KEEP YOUR OLD UI LOGIC
  // =========================

  const online = state === "ready";

  ["vera-record", "bmo-record"].forEach((id) => {
    const btn = document.getElementById(id);
    if (!btn) return;
    btn.disabled = !online;
    btn.style.opacity = online ? "1" : "0.5";
  });

  if (serverStatusEl) {
    serverStatusEl.textContent =
      state === "ready"
        ? "🟢 Server Online"
        : state === "starting"
        ? "🟡 Server Starting"
        : "🔴 Server Offline";

    serverStatusEl.className =
      `server-status ${
        state === "ready"
          ? "online"
          : state === "starting"
          ? "starting"
          : "offline"
      }`;
  }

  ["vera-server-status-inline", "bmo-server-status-inline"].forEach((id) => {
    const el = document.getElementById(id);
    if (!el) return;
    el.textContent =
      state === "ready"
        ? "🟢 Online"
        : state === "starting"
        ? "🟡 Starting"
        : "🔴 Offline";

    el.className =
      `server-status ${
        state === "ready"
          ? "online"
          : state === "starting"
          ? "starting"
          : "offline"
      } mobile-only`;
  });

  return state; // 🔥 IMPORTANT
}

checkServer();
setInterval(checkServer, 30_000);
/* =========================
   UI HELPERS
========================= */

/**
 * Flow (non–work) mode: dock input row (voice or keyboard) + lift corner tools when the voice bar
 * is in a docked state (listening / input muted) or the keyboard bar is visible.
 */
function syncVeraFlowVoiceDockLayoutClass() {
  const veraApp = document.getElementById("vera-app");
  if (!veraApp) return;
  const st = document.getElementById("vera-status");
  const voiceBar = document.getElementById("vera-voice-bar");
  const keyboardBar = document.getElementById("vera-keyboard-bar");
  if (!st || !voiceBar || !keyboardBar) return;
  const voiceVisible = !voiceBar.classList.contains("hidden");
  const keyboardVisible = !keyboardBar.classList.contains("hidden");
  if (veraApp.classList.contains("work-mode")) {
    /* Flow-mode “docked” bottom padding does not apply; keep input-active when voice/keyboard chrome is up for consistent stacking. */
    veraApp.classList.toggle("vera-flow-input-active", voiceVisible || keyboardVisible);
    veraApp.classList.remove("vera-flow-voice-docked");
    return;
  }
  /* Layer corner tools above bottom fade whenever voice or keyboard chrome is showing (e.g. Ready, not only listening). */
  veraApp.classList.toggle("vera-flow-input-active", voiceVisible || keyboardVisible);
  const rec = st.classList.contains("recording");
  const mutedIdle =
    st.classList.contains("idle") && /muted/i.test(String(st.textContent || "").trim());
  const voiceDock = voiceVisible && (rec || mutedIdle);
  const dock = voiceDock || keyboardVisible;
  veraApp.classList.toggle("vera-flow-voice-docked", dock);
  if (dock) {
    ensureChatStartedLayout();
  }
}

window.syncVeraFlowVoiceDockLayoutClass = syncVeraFlowVoiceDockLayoutClass;
/** @deprecated use syncVeraFlowVoiceDockLayoutClass */
window.syncVeraVoiceListeningLayoutClass = syncVeraFlowVoiceDockLayoutClass;

function setStatus(text, cls) {
  const statusEl = uiEl("status");
  if (!statusEl) return;
  if (cls === "thinking") {
    statusEl.innerHTML = `${text}<span class="thinking-dots" aria-hidden="true"><span>.</span><span>.</span><span>.</span></span>`;
  } else {
    statusEl.textContent = text;
  }
  statusEl.className = `status ${cls}`;
  if (statusEl.id === "vera-status") {
    if (cls === "recording" && typeof window.cancelStartupTypingForVoiceEntry === "function") {
      window.cancelStartupTypingForVoiceEntry();
    }
    syncVeraFlowVoiceDockLayoutClass();
  }
}

function applyClientUiAction(actionName) {
  const action = String(actionName || "").trim().toLowerCase();
  if (!action) return;
  if (action === "work_mode_on") {
    if (typeof window.setVeraWorkMode === "function") window.setVeraWorkMode(true);
    return;
  }
  if (action === "work_mode_off") {
    if (typeof window.setVeraWorkMode === "function") window.setVeraWorkMode(false);
  }
}

function updateMuteInputButton() {
  const continuousMicReady = listeningMode === "continuous" && !!micStream;
  const label = !continuousMicReady
    ? "Start voice input"
    : inputMuted
    ? "Unmute input"
    : "Mute input";

  ["vera-record", "bmo-record"].forEach((id) => {
    const recordBtn = document.getElementById(id);
    if (!recordBtn) return;
    recordBtn.classList.toggle("muted", continuousMicReady && inputMuted);
    recordBtn.title = label;
    recordBtn.setAttribute("aria-label", label);
    recordBtn.setAttribute(
      "aria-pressed",
      continuousMicReady && inputMuted ? "true" : "false"
    );
  });
}

function showMutedStatusIfIdle() {
  if (listeningMode !== "continuous" || !inputMuted) return;
  if (processing || !getAudioEl()?.paused) return;

  waveState = "idle";
  setStatus("Input muted", "idle");
}

function setContinuousInputMuted(nextMuted) {
  inputMuted = nextMuted;
  micStream?.getAudioTracks().forEach((track) => {
    track.enabled = !inputMuted;
  });

  if (inputMuted) {
    if (speechWaitTimeoutId != null) {
      clearTimeout(speechWaitTimeoutId);
      speechWaitTimeoutId = null;
    }
    if (rafId != null) {
      cancelAnimationFrame(rafId);
      rafId = null;
    }
    if (mediaRecorder && mediaRecorder.state === "recording") {
      suppressNextUtterance = true;
      mediaRecorder.stop();
    }

    /* Same as interrupt: stop <audio>, Web Audio chunk queue, and NDJSON TTS stream. */
    resetAudioHandlers();
    cancelMainTtsPlayback();
    const a = getAudioEl();
    if (a) {
      a.pause();
      a.currentTime = 0;
    }

    processing = false;
    listening = true;
    audioChunks = [];
    hasSpoken = false;
    lastVoiceTime = 0;
    showMutedStatusIfIdle();
  } else if (listeningMode === "continuous" && !requestInFlight && getAudioEl()?.paused) {
    listening = true;
    startListening();
  }

  updateMuteInputButton();
}

function dismissGuide() {
  const prefix = appModePrefix();
  const guideId = prefix === "bmo" ? "bmo-guide" : "vera-guide";
  const seenKey = prefix === "bmo" ? "bmo_seen_guide" : "vera_seen_guide";
  const guide = document.getElementById(guideId);
  if (!guide) return;

  guide.classList.remove("show");
  sessionStorage.setItem(seenKey, "true");

  window.setTimeout(() => {
    if (!guide.classList.contains("show")) {
      guide.classList.add("hidden");
    }
  }, 350);
}

/** Bottom-centered input dock (same as after first LLM reply) — not only after server text. */
function ensureChatStartedLayout() {
  if (!document.body.classList.contains("chat-started")) {
    document.body.classList.add("chat-started");
    dismissGuide();
  }
}

window.ensureChatStartedLayout = ensureChatStartedLayout;

function countSpeechWords(s) {
  return String(s ?? "")
    .trim()
    .split(/\s+/)
    .filter(Boolean).length;
}

function clearInterruptDetectionBubble() {
  if (!interruptDetectionBubbleEl) return;
  try {
    if (interruptDetectionBubbleEl.isConnected) {
      const row = interruptDetectionBubbleEl.closest(".message-row");
      if (row) row.remove();
      else interruptDetectionBubbleEl.remove();
    }
  } catch (_) {}
  interruptDetectionBubbleEl = null;
}

/** Live translucent user line while listening for interrupt during assistant TTS (browser ASR). */
function updateInterruptDetectionBubble(text) {
  const line = String(text ?? "").trim();
  const convo = uiEl("conversation");
  if (!convo) return;
  if (!line) return;
  if (!interruptDetectionBubbleEl?.isConnected) {
    const row = document.createElement("div");
    row.className = "message-row user";
    const bubble = document.createElement("div");
    bubble.className = "bubble user interrupt-preview";
    bubble.textContent = line;
    row.appendChild(bubble);
    convo.appendChild(row);
    interruptDetectionBubbleEl = bubble;
  } else {
    interruptDetectionBubbleEl.textContent = line;
  }
  convo.scrollTop = convo.scrollHeight;
}

function addBubble(text, who, meta) {
  const convoEl = uiEl("conversation");
  if (!convoEl) return;
  if (who === "user" && voiceTranscriptDebugEnabled()) {
    logVoiceTranscript("final", text, { ...meta, via: "addBubble" });
  }
  const row = document.createElement("div");
  row.className = `message-row ${who}`;

  const bubble = document.createElement("div");
  bubble.className = `bubble ${who}`;
  bubble.textContent = text;

  row.appendChild(bubble);
  convoEl.appendChild(row);
  convoEl.scrollTop = convoEl.scrollHeight;
  if (!chatStateHydrating && (who === "user" || who === "vera")) {
    persistVeraChatState();
  }
  return bubble;
}

/**
 * Apply final user transcript from the server (NDJSON or JSON) without removing the partial bubble:
 * updates the same DOM node the user saw while speaking, then clears the live ref so the next
 * utterance creates a new bubble. Avoids remove-then-add flash with identical text.
 */
function commitServerUserTranscriptBubble(text, path) {
  const t = String(text ?? "").trim();
  if (!t) return;
  const live = mainBrowserLiveBubble;
  if (live?.isConnected) {
    live.textContent = t;
    mainBrowserLiveBubble = null;
    if (voiceTranscriptDebugEnabled()) {
      logVoiceTranscript("final", t, { path, via: "promote-partial-bubble" });
    }
  } else {
    addBubble(t, "user", { path });
  }
  persistVeraChatState();
  ensureChatStartedLayout();
}

/** @deprecated name — use commitServerUserTranscriptBubble */
function applyNdjsonUserTranscriptBubble(text, path) {
  commitServerUserTranscriptBubble(text, path);
}

function escapeHtml(text) {
  return String(text ?? "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}

function hideSidePanel() {
  const sidePaneEl = uiEl("side-pane");
  if (!sidePaneEl) return;
  const prefix = appModePrefix();
  const isProductivityPane = sidePaneEl.dataset.sidePaneKind === "productivity";
  const keepPinnedInWorkMode =
    prefix === "vera" &&
    isProductivityPane &&
    document.getElementById("vera-app")?.classList.contains("work-mode");
  if (keepPinnedInWorkMode) {
    sidePaneEl.hidden = false;
    sidePaneEl.classList.add("visible");
    document.body.classList.remove("news-panel-open");
    document.querySelectorAll(".productivity-mode-btn").forEach((b) => b.classList.remove("is-active"));
    return;
  }
  const keepProductivityMounted = isProductivityPane && shouldKeepMusicPanelMounted(prefix);
  sidePaneEl.classList.remove("visible");
  document.body.classList.remove("news-panel-open");
  if (!keepProductivityMounted) {
    delete sidePaneEl.dataset.sidePaneKind;
  }
  document.querySelectorAll(".productivity-mode-btn").forEach((b) => b.classList.remove("is-active"));
  window.setTimeout(() => {
    if (!sidePaneEl.classList.contains("visible")) {
      sidePaneEl.hidden = true;
      if (!keepProductivityMounted && !isVeraWorkModeOn()) {
        sidePaneEl.innerHTML = "";
      }
    }
  }, 840);
}

window.hideSidePanel = hideSidePanel;

function spotifyMiniToggleId(prefix) {
  return `${prefix}-spotify-mini-toggle`;
}

function removeSpotifyMiniButton(prefix) {
  document.getElementById(spotifyMiniToggleId(prefix))?.remove();
}

function isSpotifyPlaybackActive(prefix) {
  const previewAudio = document.getElementById(`${prefix}-spotify-preview-audio`);
  if (previewAudio && !previewAudio.paused && previewAudio.currentTime > 0) return true;
  return window.__veraSpotifyPlaybackActive === true;
}

/** Keep music DOM when paused so preview/Web position is not lost on panel close. */
function shouldKeepMusicPanelMounted(prefix) {
  if (isSpotifyPlaybackActive(prefix)) return true;
  const previewAudio = document.getElementById(`${prefix}-spotify-preview-audio`);
  if (previewAudio?.src && !previewAudio.ended) return true;
  const s = spotifyEnsureNowState();
  if (window.__veraSpotifyPlayer && (s.duration_ms > 0 || s.title)) return true;
  return false;
}

function persistSpotifyResumePreview(prefix) {
  const last = window.__veraSpotifyLast || {};
  if (!last.preview_url) return;
  const a = document.getElementById(`${prefix}-spotify-preview-audio`);
  if (!a?.src || a.ended) return;
  window.__veraSpotifyResume = {
    preview_url: last.preview_url,
    currentTimeSec: a.currentTime || 0,
    paused: !!a.paused
  };
}

async function restoreSpotifyPlaybackAfterPanelRemount(prefix) {
  const resume = window.__veraSpotifyResume;
  const last = window.__veraSpotifyLast || {};
  const audio = document.getElementById(`${prefix}-spotify-preview-audio`);

  if (resume?.preview_url && last.preview_url === resume.preview_url && audio) {
    audio.volume = spotifyGetVolume();
    const targetSec = Math.max(0, Number(resume.currentTimeSec) || 0);
    const applySeek = () => {
      const dur = audio.duration;
      if (Number.isFinite(dur) && dur > 0) {
        audio.currentTime = Math.min(targetSec, Math.max(0, dur - 0.05));
      } else {
        audio.currentTime = targetSec;
      }
    };
    audio.src = resume.preview_url;
    if (audio.readyState >= 1) applySeek();
    else audio.addEventListener("loadedmetadata", applySeek, { once: true });
    spotifyUpdateNowState({
      title: last.title || "",
      artist: last.artist || "",
      position_ms: Math.round(targetSec * 1000),
      duration_ms: spotifyEnsureNowState().duration_ms,
      paused: !!resume.paused,
      active: !resume.paused
    });
    spotifySyncPlayButtonUi(prefix);
    spotifyApplyNowStateToPanel(prefix);
  }

  const wr = window.__veraSpotifyResumeWeb;
  const web = window.__veraSpotifyPlayer;
  if (web && wr && typeof web.seek === "function" && Number(wr.position_ms) > 0) {
    try {
      await web.seek(Math.floor(Number(wr.position_ms)));
    } catch (_) {
      /* ignore */
    }
    spotifyApplyNowStateToPanel(prefix);
  }
}

function restoreProductivityPanel(prefix) {
  const sidePaneEl = uiEl("side-pane");
  if (!sidePaneEl) return;
  removeSpotifyMiniButton(prefix);
  sidePaneEl.hidden = false;
  sidePaneEl.dataset.sidePaneKind = "productivity";
  document.body.classList.add("news-panel-open");
  document.querySelectorAll(".productivity-mode-btn").forEach((b) => b.classList.remove("is-active"));
  document.getElementById(`${prefix}-productivity-mode`)?.classList.add("is-active");
  spotifyApplyViewMode(prefix);
  requestAnimationFrame(() => {
    sidePaneEl.classList.add("visible");
  });
}

function renderNewsResultListMarkup(results) {
  if (!results.length) {
    return `<div class="side-pane-empty">No articles available for this search.</div>`;
  }

  return `
    <div class="news-result-list">
      ${results.map((item, index) => `
        <article class="news-result-card">
          <h4 class="news-result-title">${index + 1}. ${escapeHtml(item.title)}</h4>
          <p class="news-result-snippet">${escapeHtml(item.summary)}</p>
          <div class="news-result-meta">
            <span>${escapeHtml(item.source || "Unknown source")}</span>
            <span>${escapeHtml(item.published_display || "")}</span>
          </div>
          ${item.url ? `<a class="news-result-link" href="${escapeHtml(item.url)}" target="_blank" rel="noopener noreferrer">Open source</a>` : ""}
        </article>
      `).join("")}
    </div>
  `;
}

function renderImageResultsMarkup(images) {
  if (!images.length) {
    return `<div class="side-pane-empty">No images available for this search.</div>`;
  }

  return `
    <div class="media-grid">
      ${images.map((item) => `
        <article class="media-card image-card">
          <a
            class="media-link"
            href="${escapeHtml(item.url || item.image_url)}"
            target="_blank"
            rel="noopener noreferrer"
          >
            <img
              class="media-image"
              src="${escapeHtml(item.image_url || item.thumbnail_url || "")}"
              alt="${escapeHtml(item.title || "Search result image")}"
              loading="lazy"
              referrerpolicy="no-referrer"
            />
          </a>
          <div class="media-card-body">
            <div class="media-card-title">${escapeHtml(item.title || "Image result")}</div>
            <div class="media-card-meta">${escapeHtml(item.source || "Unknown source")}</div>
          </div>
        </article>
      `).join("")}
    </div>
  `;
}

function getVideoEmbedUrl(url) {
  if (!url) return "";

  try {
    const parsed = new URL(url);
    const host = parsed.hostname.replace(/^www\./, "");

    if (host === "youtu.be") {
      const videoId = parsed.pathname.replaceAll("/", "");
      return videoId ? `https://www.youtube.com/embed/${videoId}` : "";
    }

    if (host === "youtube.com" || host === "m.youtube.com") {
      const videoId = parsed.searchParams.get("v");
      return videoId ? `https://www.youtube.com/embed/${videoId}` : "";
    }
  } catch {
    return "";
  }

  return "";
}

function renderVideoResultsMarkup(videos) {
  if (!videos.length) {
    return `<div class="side-pane-empty">No videos available for this search.</div>`;
  }

  return `
    <div class="video-result-list">
      ${videos.map((item) => {
        const embedUrl = getVideoEmbedUrl(item.url);
        return `
          <article class="media-card video-card">
            ${embedUrl ? `
              <div class="video-embed-wrap">
                <iframe
                  class="video-embed"
                  src="${escapeHtml(embedUrl)}"
                  title="${escapeHtml(item.title)}"
                  allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture"
                  allowfullscreen
                  loading="lazy"
                  referrerpolicy="strict-origin-when-cross-origin"
                ></iframe>
              </div>
            ` : item.thumbnail_url ? `
              <a
                class="media-link"
                href="${escapeHtml(item.url)}"
                target="_blank"
                rel="noopener noreferrer"
              >
                <img
                  class="media-image"
                  src="${escapeHtml(item.thumbnail_url)}"
                  alt="${escapeHtml(item.title)}"
                  loading="lazy"
                  referrerpolicy="no-referrer"
                />
              </a>
            ` : ""}
            <div class="media-card-body">
              <div class="media-card-title">${escapeHtml(item.title)}</div>
              <div class="media-card-meta">
                <span>${escapeHtml(item.source || "Unknown source")}</span>
                <span>${escapeHtml(item.published_display || "")}</span>
              </div>
              ${item.summary ? `<p class="news-result-snippet">${escapeHtml(item.summary)}</p>` : ""}
              <a class="news-result-link" href="${escapeHtml(item.url)}" target="_blank" rel="noopener noreferrer">Open video</a>
            </div>
          </article>
        `;
      }).join("")}
    </div>
  `;
}

function setActiveSidePaneTab(tabName) {
  const sidePaneEl = uiEl("side-pane");
  if (!sidePaneEl) return;

  sidePaneEl.querySelectorAll(".side-pane-tab").forEach((button) => {
    const isActive = button.dataset.tab === tabName;
    button.classList.toggle("active", isActive);
    button.setAttribute("aria-selected", isActive ? "true" : "false");
  });

  sidePaneEl.querySelectorAll(".side-pane-tab-panel").forEach((panel) => {
    panel.classList.toggle("active", panel.dataset.tabPanel === tabName);
  });
}

function renderMediaTabsPanel(payload) {
  const sidePaneEl = uiEl("side-pane");
  if (!sidePaneEl) return;

  const mount = () => {
    document.querySelectorAll(".productivity-mode-btn").forEach((b) => b.classList.remove("is-active"));

    const results = Array.isArray(payload?.news_results)
      ? payload.news_results
      : Array.isArray(payload?.results)
        ? payload.results
        : [];
    const images = Array.isArray(payload?.images) ? payload.images : [];
    const videos = Array.isArray(payload?.videos) ? payload.videos : [];
    const defaultTab = payload?.default_tab || "news";

    sidePaneEl.hidden = false;
    delete sidePaneEl.dataset.sidePaneKind;
    document.body.classList.add("news-panel-open");

    sidePaneEl.innerHTML = `
    <div class="side-pane-header">
      <div class="side-pane-heading">
        <h3 class="side-pane-title">${escapeHtml(payload?.title || "News Results")}</h3>
        <div class="side-pane-subtitle">${escapeHtml(payload?.query || "Top headlines")}</div>
      </div>
      <div class="side-pane-controls">
        <div class="side-pane-tabs" role="tablist" aria-label="Search result tabs">
          <button class="side-pane-tab ${defaultTab === "news" ? "active" : ""}" type="button" role="tab" aria-selected="${defaultTab === "news" ? "true" : "false"}" data-tab="news">News</button>
          <button class="side-pane-tab ${defaultTab === "images" ? "active" : ""}" type="button" role="tab" aria-selected="${defaultTab === "images" ? "true" : "false"}" data-tab="images">Images</button>
          <button class="side-pane-tab ${defaultTab === "video" ? "active" : ""}" type="button" role="tab" aria-selected="${defaultTab === "video" ? "true" : "false"}" data-tab="video">Video</button>
        </div>
        <button class="side-pane-close" type="button" aria-label="Close panel">×</button>
      </div>
    </div>
    <div class="side-pane-tab-panel ${defaultTab === "news" ? "active" : ""}" data-tab-panel="news">
      ${renderNewsResultListMarkup(results)}
    </div>
    <div class="side-pane-tab-panel ${defaultTab === "images" ? "active" : ""}" data-tab-panel="images">
      ${renderImageResultsMarkup(images)}
    </div>
    <div class="side-pane-tab-panel ${defaultTab === "video" ? "active" : ""}" data-tab-panel="video">
      ${renderVideoResultsMarkup(videos)}
    </div>
  `;

    sidePaneEl.scrollTop = 0;

    requestAnimationFrame(() => {
      sidePaneEl.classList.add("visible");
    });
  };

  runFlowModeSidePaneContentCrossfade(sidePaneEl, mount);
}

function renderFinanceChartPanel(payload) {
  const sidePaneEl = uiEl("side-pane");
  if (!sidePaneEl) return;

  const mount = () => {
    document.querySelectorAll(".productivity-mode-btn").forEach((b) => b.classList.remove("is-active"));

    const frameSrc = payload?.chart_url
      ? (payload.chart_url.startsWith("/") ? `${API_URL}${payload.chart_url}` : payload.chart_url)
      : "";

    sidePaneEl.hidden = false;
    delete sidePaneEl.dataset.sidePaneKind;
    document.body.classList.add("news-panel-open");

    sidePaneEl.innerHTML = `
    <div class="side-pane-header">
      <div class="side-pane-heading">
        <h3 class="side-pane-title">${escapeHtml(payload?.title || "Stock Chart")}</h3>
        <div class="side-pane-subtitle">${escapeHtml(payload?.query || payload?.symbol || "Quote lookup")}</div>
      </div>
      <div class="side-pane-controls">
        <button class="side-pane-close" type="button" aria-label="Close panel">×</button>
      </div>
    </div>
    <div class="finance-chart-panel">
      ${frameSrc ? `
        <div class="finance-chart-wrap">
          <iframe
            class="finance-chart-frame"
            src="${escapeHtml(frameSrc)}"
            title="${escapeHtml(payload?.symbol || payload?.query || "Stock chart")}"
            loading="lazy"
            referrerpolicy="strict-origin-when-cross-origin"
          ></iframe>
        </div>
      ` : `
        <div class="side-pane-empty">
          I couldn’t resolve a chart symbol for this quote yet.
          ${payload?.source_url ? `<a class="news-result-link" href="${escapeHtml(payload.source_url)}" target="_blank" rel="noopener noreferrer">Open finance source</a>` : ""}
        </div>
      `}
    </div>
  `;

    sidePaneEl.scrollTop = 0;

    requestAnimationFrame(() => {
      sidePaneEl.classList.add("visible");
    });
  };

  runFlowModeSidePaneContentCrossfade(sidePaneEl, mount);
}

/** spotify URIs -> open.spotify.com when API omits external_urls */
function spotifyUriToOpenUrl(uri) {
  const s = String(uri || "");
  const mT = s.match(/^spotify:track:([a-zA-Z0-9]+)$/);
  if (mT) return `https://open.spotify.com/track/${mT[1]}`;
  const mAr = s.match(/^spotify:artist:([a-zA-Z0-9]+)$/);
  if (mAr) return `https://open.spotify.com/artist/${mAr[1]}`;
  const mAl = s.match(/^spotify:album:([a-zA-Z0-9]+)$/);
  if (mAl) return `https://open.spotify.com/album/${mAl[1]}`;
  const mPl = s.match(/^spotify:playlist:([a-zA-Z0-9]+)$/);
  if (mPl) return `https://open.spotify.com/playlist/${mPl[1]}`;
  return "";
}

/** Spotify catalog id from ``spotify:album:…`` / ``spotify:artist:…`` / ``spotify:track:…``. */
function spotifyEntityIdFromUri(uri, entity) {
  const p = `spotify:${entity}:`;
  const s = String(uri || "").trim();
  if (!s.startsWith(p)) return "";
  return s.slice(p.length).split(/[?#]/)[0] || "";
}

function spotifyRememberSearchSnapshot(prefix) {
  const el = document.getElementById(`${prefix}-spotify-results`);
  if (!el) return;
  window.__veraSpotifySearchSnapshot ||= {};
  window.__veraSpotifySearchSnapshot[prefix] = el.innerHTML;
}

function spotifyRestoreSearchSnapshot(prefix) {
  const el = document.getElementById(`${prefix}-spotify-results`);
  const snap = window.__veraSpotifySearchSnapshot?.[prefix];
  if (el && typeof snap === "string" && snap.length) el.innerHTML = snap;
}

function spotifyRestorePlaylistListSnapshot(prefix) {
  const root = document.getElementById(`${prefix}-spotify-playlist-root`);
  const snap = window.__veraSpotifyPlaylistSnapshot?.[prefix];
  if (root && typeof snap === "string" && snap.length) root.innerHTML = snap;
  spotifySyncPlaylistSelectionHighlight(prefix);
}

function spotifyDetailTrackRowsHtml(tracks, from, to) {
  const slice = (tracks || []).slice(from, to);
  return slice
    .map((item) => {
      const titlePlain = String(item.name ?? item.title ?? "Track");
      const titleEsc = escapeHtml(titlePlain);
      const artistEsc = escapeHtml(spotifyFormatArtists(item));
      const uri = item.uri != null ? escapeHtml(String(item.uri)) : "";
      const prev = item.preview_url != null ? escapeHtml(String(item.preview_url)) : "";
      const openRaw = String(item.open_url || spotifyUriToOpenUrl(item.uri) || "").trim();
      const openEsc = openRaw ? escapeHtml(openRaw) : "";
      return `
        <button type="button" class="spotify-detail-track-row" data-spotify-uri="${uri}" data-preview-url="${prev}" data-open-url="${openEsc}" data-display-title="${titleEsc}" data-display-sub="${artistEsc}">
          <div class="spotify-result-text">
            <div class="spotify-result-title"><span class="spotify-result-title-text">${titleEsc}</span></div>
            <div class="spotify-result-sub">${artistEsc}</div>
          </div>
        </button>`;
    })
    .join("");
}

function spotifyArtistAlbumRowsHtml(albums) {
  const list = Array.isArray(albums) ? albums : [];
  return list
    .map((item) => {
      const titlePlain = String(item.name ?? item.title ?? "Album");
      const titleEsc = escapeHtml(titlePlain);
      const subPlain =
        item.subtitle != null && String(item.subtitle).trim()
          ? String(item.subtitle).trim()
          : spotifyFormatArtists(item) || "Album";
      const subEsc = escapeHtml(subPlain);
      const uriRaw = String(item.uri || "").trim();
      const uri = escapeHtml(uriRaw);
      const thumbUrl = String(item.imageUrl || item.image || "").trim();
      const thumbEsc = thumbUrl ? escapeHtml(thumbUrl) : "";
      return `
        <button type="button" class="spotify-result-row spotify-result-row--album spotify-artist-album-row" data-spotify-album-uri="${uri}" data-display-title="${titleEsc}" data-display-sub="${subEsc}" data-thumb-url="${thumbEsc}">
          ${thumbEsc
            ? `<img class="spotify-result-thumb" src="${thumbEsc}" alt="" loading="lazy" />`
            : `<div class="spotify-result-thumb" aria-hidden="true"></div>`}
          <div class="spotify-result-text">
            <div class="spotify-result-title">
              <span class="spotify-result-kind">Album</span>
              <span class="spotify-result-title-text">${titleEsc}</span>
            </div>
            <div class="spotify-result-sub">${subEsc}</div>
          </div>
        </button>`;
    })
    .join("");
}

async function spotifyOpenAlbumSearchDetail(prefix, meta) {
  const resultsEl = document.getElementById(`${prefix}-spotify-results`);
  if (!resultsEl) return;
  const albumUri = String(meta?.albumUri || "").trim();
  const title = String(meta?.title || "Album");
  const sub = String(meta?.sub || "");
  const thumbUrl = String(meta?.thumbUrl || "").trim();
  const aid = spotifyEntityIdFromUri(albumUri, "album");
  if (!aid) return;
  resultsEl.innerHTML = `<p class="spotify-results-hint">Loading album…</p>`;
  const fn = window.VeraSpotify?.getAlbumTracks;
  if (typeof fn !== "function") {
    resultsEl.innerHTML = `<p class="spotify-results-error">Album tracks API unavailable.</p>`;
    return;
  }
  let tracks;
  try {
    tracks = await fn(aid);
  } catch (err) {
    resultsEl.innerHTML = `<p class="spotify-results-error">${escapeHtml(String(err?.message ?? err))}</p>`;
    return;
  }
  const list = Array.isArray(tracks) ? tracks : [];
  const thumb = thumbUrl
    ? `<img class="spotify-search-detail-cover" src="${escapeHtml(thumbUrl)}" alt="" loading="lazy" />`
    : `<div class="spotify-search-detail-cover spotify-search-detail-cover--ph" aria-hidden="true"></div>`;
  const titleEsc = escapeHtml(title);
  const subEsc = escapeHtml(sub);
  const uriEsc = escapeHtml(albumUri);
  resultsEl.innerHTML = `
    <div class="spotify-search-detail" data-spotify-detail="album">
      <button type="button" class="spotify-search-back">← Results</button>
      <div class="spotify-search-detail-head">
        ${thumb}
        <div class="spotify-search-detail-meta">
          <div class="spotify-search-detail-title">${titleEsc}</div>
          <div class="spotify-search-detail-sub">${subEsc}</div>
        </div>
        <button type="button" class="spotify-album-play-triangle" data-spotify-album-uri="${uriEsc}" aria-label="Play album">▶</button>
      </div>
      <div class="spotify-detail-tracklist">${list.length ? spotifyDetailTrackRowsHtml(list, 0, list.length) : `<p class="spotify-results-hint">No tracks on this album.</p>`}</div>
    </div>`;
}

async function spotifyOpenPlaylistSideDetail(prefix, meta) {
  const root = document.getElementById(`${prefix}-spotify-playlist-root`);
  if (!root) return;
  window.__veraSpotifyPlaylistSnapshot ||= {};
  window.__veraSpotifyPlaylistSnapshot[prefix] = root.innerHTML;

  const playlistId = String(meta?.playlistId || "").trim();
  const playlistUri = String(meta?.playlistUri || "").trim();
  const title = String(meta?.title || "Playlist");
  const sub = String(meta?.sub || "");
  const thumbUrl = String(meta?.thumbUrl || "").trim();
  if (!playlistId || !playlistUri) return;

  root.innerHTML = `<p class="spotify-results-hint">Loading tracks…</p>`;
  const fn = window.VeraSpotify?.getPlaylistTracks;
  if (typeof fn !== "function") {
    spotifyRestorePlaylistListSnapshot(prefix);
    const r = document.getElementById(`${prefix}-spotify-playlist-root`);
    if (r) {
      r.insertAdjacentHTML(
        "beforeend",
        `<p class="spotify-results-error">Playlist tracks API is unavailable.</p>`
      );
    }
    return;
  }
  let tracks;
  try {
    tracks = await fn(playlistId);
  } catch (err) {
    spotifyRestorePlaylistListSnapshot(prefix);
    const r = document.getElementById(`${prefix}-spotify-playlist-root`);
    if (r) {
      r.insertAdjacentHTML(
        "beforeend",
        `<p class="spotify-results-error">${escapeHtml(String(err?.message ?? err))}</p>`
      );
    }
    return;
  }
  const list = Array.isArray(tracks) ? tracks : [];
  const thumb = thumbUrl
    ? `<img class="spotify-search-detail-cover" src="${escapeHtml(thumbUrl)}" alt="" loading="lazy" />`
    : `<div class="spotify-search-detail-cover spotify-search-detail-cover--ph" aria-hidden="true"></div>`;
  const titleEsc = escapeHtml(title);
  const subEsc = escapeHtml(sub);
  const uriEsc = escapeHtml(playlistUri);
  root.innerHTML = `
    <div class="spotify-search-detail" data-spotify-detail="playlist" data-spotify-playlist-context-uri="${uriEsc}">
      <button type="button" class="spotify-search-back">← Playlists</button>
      <div class="spotify-search-detail-head">
        ${thumb}
        <div class="spotify-search-detail-meta">
          <div class="spotify-search-detail-title">${titleEsc}</div>
          <div class="spotify-search-detail-sub">${subEsc}</div>
        </div>
        <button type="button" class="spotify-album-play-triangle" data-spotify-album-uri="${uriEsc}" aria-label="Play playlist">▶</button>
      </div>
      <div class="spotify-detail-tracklist">${
        list.length
          ? spotifyDetailTrackRowsHtml(list, 0, list.length)
          : `<p class="spotify-results-hint">This playlist has no playable tracks yet.</p>`
      }</div>
    </div>`;
}

async function spotifyOpenArtistSearchDetail(prefix, meta) {
  const resultsEl = document.getElementById(`${prefix}-spotify-results`);
  if (!resultsEl) return;
  const artistUri = String(meta?.artistUri || "").trim();
  const title = String(meta?.title || "Artist");
  const thumbUrl = String(meta?.thumbUrl || "").trim();
  const arid = spotifyEntityIdFromUri(artistUri, "artist");
  if (!arid) return;
  resultsEl.innerHTML = `<p class="spotify-results-hint">Loading…</p>`;
  const fn = window.VeraSpotify?.getArtistAlbums;
  if (typeof fn !== "function") {
    resultsEl.innerHTML = `<p class="spotify-results-error">Artist albums API unavailable.</p>`;
    return;
  }
  let albums;
  try {
    albums = await fn(arid);
  } catch (err) {
    resultsEl.innerHTML = `<p class="spotify-results-error">${escapeHtml(String(err?.message ?? err))}</p>`;
    return;
  }
  const list = Array.isArray(albums) ? albums : [];
  const rows = spotifyArtistAlbumRowsHtml(list);
  const thumb = thumbUrl
    ? `<img class="spotify-search-detail-cover" src="${escapeHtml(thumbUrl)}" alt="" loading="lazy" />`
    : `<div class="spotify-search-detail-cover spotify-search-detail-cover--ph" aria-hidden="true"></div>`;
  const titleEsc = escapeHtml(title);
  resultsEl.innerHTML = `
    <div class="spotify-search-detail" data-spotify-detail="artist">
      <button type="button" class="spotify-search-back">← Results</button>
      <div class="spotify-search-detail-head">
        ${thumb}
        <div class="spotify-search-detail-meta">
          <div class="spotify-search-detail-title">${titleEsc}</div>
          <div class="spotify-search-detail-sub">Albums</div>
        </div>
      </div>
      <div class="spotify-detail-tracklist">${rows || `<p class="spotify-results-hint">No albums found.</p>`}</div>
    </div>`;
}

function spotifyFormatArtists(item) {
  const a = item?.artist ?? item?.artists;
  if (Array.isArray(a)) {
    return a
      .map((x) => (typeof x === "string" ? x : x?.name))
      .filter(Boolean)
      .join(", ");
  }
  return a != null ? String(a) : "";
}

function renderSpotifySearchResults(prefix, items) {
  const resultsEl = document.getElementById(`${prefix}-spotify-results`);
  if (!resultsEl) return;
  const list = Array.isArray(items) ? items : [];
  if (!list.length) {
    resultsEl.innerHTML = `<p class="spotify-results-hint">No results. If you use Spotify keys in a <strong>local</strong> <code>.env</code>, open this page from <code>http://127.0.0.1:8000</code> so search hits your FastAPI (not only the cloud worker).</p>`;
    return;
  }
  resultsEl.innerHTML = list
    .map((item, i) => {
      const kind = String(item.kind || "track").toLowerCase();
      const titlePlain = String(item.title ?? item.name ?? "Result");
      const titleEsc = escapeHtml(titlePlain);
      const subPlain =
        item.subtitle != null && String(item.subtitle).trim()
          ? String(item.subtitle).trim()
          : spotifyFormatArtists(item) || (kind === "artist" ? "Artist" : kind === "album" ? "Album" : "");
      const subEsc = escapeHtml(subPlain);
      const uri = item.uri != null ? escapeHtml(String(item.uri)) : "";
      const img = item.imageUrl ?? item.image ?? item.album?.images?.[0]?.url ?? "";
      const thumb = img
        ? `<img class="spotify-result-thumb" src="${escapeHtml(img)}" alt="" loading="lazy" />`
        : `<div class="spotify-result-thumb" aria-hidden="true"></div>`;
      const prev = item.preview_url != null ? escapeHtml(String(item.preview_url)) : "";
      const openRaw = String(item.open_url || spotifyUriToOpenUrl(item.uri) || "").trim();
      const openEsc = openRaw ? escapeHtml(openRaw) : "";
      const kindChip =
        kind === "album" || kind === "artist"
          ? `<span class="spotify-result-kind">${kind === "album" ? "Album" : "Artist"}</span>`
          : "";
      return `
        <button type="button" class="spotify-result-row spotify-result-row--${escapeHtml(kind)}" data-spotify-kind="${escapeHtml(
        kind
      )}" data-spotify-uri="${uri}" data-spotify-index="${i}" data-preview-url="${prev}" data-open-url="${openEsc}" data-display-title="${titleEsc}" data-display-sub="${subEsc}">
          ${thumb}
          <div class="spotify-result-text">
            <div class="spotify-result-title">
              ${kindChip}
              <span class="spotify-result-title-text">${titleEsc}</span>
            </div>
            <div class="spotify-result-sub">${subEsc}</div>
          </div>
        </button>`;
    })
    .join("");
}

function renderSpotifyPlaylistResults(prefix, playlists) {
  const root = document.getElementById(`${prefix}-spotify-playlist-root`);
  if (!root) return;
  const list = Array.isArray(playlists) ? playlists : [];
  if (!list.length) {
    root.innerHTML = `<p class="spotify-results-hint">No playlists found for this account.</p>`;
    return;
  }
  root.innerHTML = list
    .map((p) => {
      const name = escapeHtml(p.name || "Playlist");
      const uri = escapeHtml(String(p.uri || ""));
      const pid = escapeHtml(String(p.id || ""));
      const total = Number(p.tracks_total) || 0;
      const owner = escapeHtml(String(p.owner_name || ""));
      const img = p.image_url
        ? `<img class="spotify-result-thumb" src="${escapeHtml(p.image_url)}" alt="" loading="lazy" />`
        : `<div class="spotify-result-thumb" aria-hidden="true"></div>`;
      return `
        <button type="button" class="spotify-result-row spotify-playlist-row" data-playlist-id="${pid}" data-playlist-uri="${uri}">
          ${img}
          <div class="spotify-result-text">
            <div class="spotify-result-title">${name}</div>
            <div class="spotify-result-sub">${total} tracks${owner ? ` • ${owner}` : ""}</div>
          </div>
        </button>
      `;
    })
    .join("");
  spotifySyncPlaylistSelectionHighlight(prefix);
}

let _veraSpotifySdkLoading = null;

function loadSpotifyWebSdkScript() {
  if (window.Spotify) return Promise.resolve();
  if (_veraSpotifySdkLoading) return _veraSpotifySdkLoading;
  _veraSpotifySdkLoading = new Promise((resolve, reject) => {
    const s = document.createElement("script");
    s.src = "https://sdk.scdn.co/spotify-player.js";
    s.async = true;
    s.dataset.veraSpotifySdk = "1";
    window.onSpotifyWebPlaybackSDKReady = () => {
      _veraSpotifySdkLoading = null;
      resolve();
    };
    s.onerror = () => {
      _veraSpotifySdkLoading = null;
      reject(new Error("Spotify Web Playback SDK failed to load"));
    };
    document.body.appendChild(s);
  });
  return _veraSpotifySdkLoading;
}

const VERA_SPOTIFY_BEARER_STORAGE_KEY = "vera_spotify_bearer";

/** Prefer localStorage so Spotify stays “connected” across reloads and new tabs (same browser). */
function veraSpotifyGetStoredBearer() {
  try {
    return localStorage.getItem(VERA_SPOTIFY_BEARER_STORAGE_KEY) || sessionStorage.getItem(VERA_SPOTIFY_BEARER_STORAGE_KEY);
  } catch (_) {
    return null;
  }
}

function veraSpotifySetStoredBearer(token) {
  const t = String(token || "").trim();
  if (!t) return;
  try {
    localStorage.setItem(VERA_SPOTIFY_BEARER_STORAGE_KEY, t);
    sessionStorage.setItem(VERA_SPOTIFY_BEARER_STORAGE_KEY, t);
  } catch (_) {
    try {
      sessionStorage.setItem(VERA_SPOTIFY_BEARER_STORAGE_KEY, t);
    } catch (_) {
      /* ignore */
    }
  }
}

function veraSpotifyAuthHeaders() {
  const t = veraSpotifyGetStoredBearer();
  if (t) return { Authorization: `Bearer ${t}` };
  return {};
}

function clearVeraSpotifyBearer() {
  try {
    localStorage.removeItem(VERA_SPOTIFY_BEARER_STORAGE_KEY);
    sessionStorage.removeItem(VERA_SPOTIFY_BEARER_STORAGE_KEY);
  } catch (_) {
    /* ignore */
  }
  window.__veraSpotifyBearer = null;
}

async function claimSpotifyHandoff(handoff) {
  if (!handoff || typeof handoff !== "string") return;
  const base = localBackendBase();
  const res = await fetch(`${base}/api/spotify/claim-handoff`, {
    method: "POST",
    credentials: "include",
    headers: { "Content-Type": "application/json", ...veraSpotifyAuthHeaders() },
    body: JSON.stringify({ handoff })
  });
  if (!res.ok) return;
  const j = await res.json().catch(() => ({}));
  if (j.bearer) {
    veraSpotifySetStoredBearer(j.bearer);
    window.__veraSpotifyBearer = j.bearer;
  }
}

async function refreshSpotifyConnectionUI(prefix) {
  const base = localBackendBase();
  const res = await fetch(`${base}/api/spotify/connection-status`, {
    credentials: "include",
    headers: { ...veraSpotifyAuthHeaders() }
  }).catch(() => null);
  const j = res?.ok ? await res.json().catch(() => ({})) : { connected: false };
  const badge = document.getElementById(`${prefix}-spotify-connected-badge`);
  const logout = document.getElementById(`${prefix}-spotify-logout`);
  const link = document.getElementById(`${prefix}-spotify-connect-link`);
  if (badge) badge.hidden = !j.connected;
  if (logout) logout.hidden = !j.connected;
  if (link) link.style.display = j.connected ? "none" : "";
}

function spotifySyncPlayButtonUi(prefix) {
  const playBtn = document.getElementById(`${prefix}-spotify-play`);
  if (!playBtn) return;
  if (window.__veraSpotifyPlayer) return;
  const audio = document.getElementById(`${prefix}-spotify-preview-audio`);
  if (!audio?.src) {
    playBtn.textContent = "▶";
    playBtn.setAttribute("aria-label", "Play / pause");
    return;
  }
  playBtn.textContent = audio.paused ? "▶" : "⏸";
  playBtn.setAttribute("aria-label", audio.paused ? "Play" : "Pause");
}

function spotifyFormatTimeMs(ms) {
  const total = Math.max(0, Number(ms) || 0);
  const s = Math.floor(total / 1000);
  const m = Math.floor(s / 60);
  const sec = String(s % 60).padStart(2, "0");
  return `${m}:${sec}`;
}

const SPOTIFY_VOLUME_DEFAULT = 0.1;
const SPOTIFY_VOLUME_MAX = 0.35;

function spotifyGetVolume() {
  const v = Number(window.__veraSpotifyVolume);
  if (Number.isFinite(v) && v >= 0 && v <= SPOTIFY_VOLUME_MAX) return v;
  const clamped = Number.isFinite(v) ? Math.max(0, Math.min(SPOTIFY_VOLUME_MAX, v)) : SPOTIFY_VOLUME_DEFAULT;
  window.__veraSpotifyVolume = clamped;
  return clamped;
}

function spotifyEnsureNowState() {
  if (!window.__veraSpotifyNowState) {
    window.__veraSpotifyNowState = {
      title: "",
      artist: "",
      cover_url: "",
      position_ms: 0,
      duration_ms: 0,
      paused: true,
      active: false
    };
  }
  return window.__veraSpotifyNowState;
}

function buildClientContextSnapshot() {
  const prefix = appModePrefix();
  const inWorkMode = prefix === "vera" && isVeraWorkModeOn();
  const now = spotifyEnsureNowState();
  const musicTitleDom = document.getElementById(`${prefix}-spotify-track-title`)?.textContent || "";
  const musicArtistDom = document.getElementById(`${prefix}-spotify-track-artist`)?.textContent || "";

  let checklistItems = [];
  if (inWorkMode) {
    try {
      const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY) || "[]";
      const parsed = JSON.parse(raw);
      if (Array.isArray(parsed)) checklistItems = parsed;
    } catch (_) {}
  }
  const ongoing = checklistItems
    .filter((x) => x && !Boolean(x.done))
    .map((x) => String(x.text || "").trim())
    .filter(Boolean);
  const completed = checklistItems
    .filter((x) => x && Boolean(x.done))
    .map((x) => String(x.text || "").trim())
    .filter(Boolean);

  return {
    mode: inWorkMode ? "work" : "flow",
    app: prefix,
    music: {
      title: String(now.title || musicTitleDom || "").trim(),
      artist: String(now.artist || musicArtistDom || "").trim(),
      is_playing: Boolean(now.active) && !Boolean(now.paused),
      paused: Boolean(now.paused),
      position_ms: Number(now.position_ms) || 0,
      duration_ms: Number(now.duration_ms) || 0,
    },
    checklist: inWorkMode
      ? {
          ongoing_count: ongoing.length,
          completed_count: completed.length,
          ongoing_items: ongoing.slice(0, 8),
        }
      : null,
  };
}

function spotifyUpdateNowState(partial = {}) {
  const cur = spotifyEnsureNowState();
  window.__veraSpotifyNowState = { ...cur, ...partial };
  return window.__veraSpotifyNowState;
}

/** After user starts a ``spotify:track:`` on Web Playback, ignore mismatched SDK metadata until catch-up (prevents title/cover flicker). */
function spotifyClearPendingSdkTrack() {
  window.__veraSpotifyPendingSdkTrack = null;
}

function spotifySetPendingSdkTrack(uri) {
  const u = String(uri || "").trim();
  if (!u.startsWith("spotify:track:")) {
    spotifyClearPendingSdkTrack();
    return;
  }
  window.__veraSpotifyPendingSdkTrack = { uri: u, until: Date.now() + 3800 };
}

function spotifySdkMetadataStaleVersusPending(sdkTrackUri) {
  const p = window.__veraSpotifyPendingSdkTrack;
  if (!p?.uri) return false;
  if (Date.now() > p.until) {
    spotifyClearPendingSdkTrack();
    return false;
  }
  const s = String(sdkTrackUri || "").trim();
  return Boolean(s) && s !== p.uri;
}

function spotifyClearPendingIfSdkMatches(sdkTrackUri) {
  const p = window.__veraSpotifyPendingSdkTrack;
  if (!p?.uri) return;
  if (Date.now() > p.until) {
    spotifyClearPendingSdkTrack();
    return;
  }
  if (String(sdkTrackUri || "").trim() === p.uri) spotifyClearPendingSdkTrack();
}

/** Merge Spotify Web Playback ``state`` into ``__veraSpotifyNowState`` (metadata skipped when pending URI mismatches SDK). */
function spotifySyncNowStateFromWebSdk(state) {
  if (!state) return;
  const curTrack = state.track_window?.current_track;
  const position_ms = Number(state.position) || 0;
  const paused = !!state.paused;

  if (!curTrack) {
    spotifyUpdateNowState({
      position_ms,
      paused,
      active: false
    });
    window.__veraSpotifyPlaybackActive = false;
    return;
  }

  const sdkUri = String(curTrack.uri || "").trim();
  const active = !paused;
  if (spotifySdkMetadataStaleVersusPending(sdkUri)) {
    spotifyUpdateNowState({
      position_ms,
      paused,
      active
    });
    window.__veraSpotifyPlaybackActive = active;
    return;
  }

  spotifyClearPendingIfSdkMatches(sdkUri);
  const cover = curTrack.album?.images?.[0]?.url || "";
  spotifyUpdateNowState({
    title: curTrack.name || "",
    artist: (curTrack.artists || []).map((a) => a.name).filter(Boolean).join(", "),
    cover_url: cover,
    position_ms,
    duration_ms: Number(curTrack.duration_ms) || 0,
    paused,
    active
  });
  window.__veraSpotifyPlaybackActive = active;
}

function spotifyStopWebPlaybackUiTick() {
  if (window.__veraSpotifyUiTick != null) {
    window.clearInterval(window.__veraSpotifyUiTick);
    window.__veraSpotifyUiTick = null;
  }
  window.__veraSpotifyUiTickPrefix = null;
}

/**
 * While Web Playback is running, ``player_state_changed`` is sparse; poll ``getCurrentState`` so the
 * progress bar and elapsed time update smoothly (~4×/s, paused when the tab is hidden).
 */
function spotifyStartWebPlaybackUiTick(prefix) {
  spotifyStopWebPlaybackUiTick();
  const pfx = prefix || appModePrefix();
  window.__veraSpotifyUiTickPrefix = pfx;
  let inFlight = false;
  window.__veraSpotifyUiTick = window.setInterval(async () => {
    if (typeof document !== "undefined" && document.hidden) return;
    if (inFlight) return;
    const player = window.__veraSpotifyPlayer;
    const tickPrefix = window.__veraSpotifyUiTickPrefix || appModePrefix();
    if (!player || typeof player.getCurrentState !== "function") {
      spotifyStopWebPlaybackUiTick();
      return;
    }
    inFlight = true;
    try {
      const state = await player.getCurrentState();
      if (!state) {
        spotifyStopWebPlaybackUiTick();
        return;
      }
      spotifySyncNowStateFromWebSdk(state);
      spotifyApplyNowStateToPanel(tickPrefix);
      const curTrack = state.track_window?.current_track;
      if (state.paused || !curTrack) spotifyStopWebPlaybackUiTick();
    } catch (_) {
      spotifyStopWebPlaybackUiTick();
    } finally {
      inFlight = false;
    }
  }, 250);
}

function spotifyApplyNowStateToPanel(prefix) {
  const s = spotifyEnsureNowState();
  const titleEl = document.getElementById(`${prefix}-spotify-track-title`);
  const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
  const ph = document.getElementById(`${prefix}-spotify-art-placeholder`);
  const progress = document.getElementById(`${prefix}-spotify-progress`);
  const elapsed = document.getElementById(`${prefix}-spotify-time-elapsed`);
  const total = document.getElementById(`${prefix}-spotify-time-total`);
  const playBtn = document.getElementById(`${prefix}-spotify-play`);

  if (titleEl) titleEl.textContent = s.title || "Nothing playing";
  if (artistEl) {
    artistEl.textContent =
      s.artist ||
      "Connect Spotify for in-browser playback, or use search + preview / Open in Spotify.";
  }
  if (ph && s.cover_url) {
    ph.style.backgroundImage = `url(${JSON.stringify(s.cover_url)})`;
    ph.style.backgroundSize = "cover";
  }
  if (elapsed) elapsed.textContent = spotifyFormatTimeMs(s.position_ms);
  if (total) total.textContent = spotifyFormatTimeMs(s.duration_ms);
  if (progress) {
    const duration = Math.max(0, Number(s.duration_ms) || 0);
    progress.max = String(duration);
    if (document.activeElement !== progress) {
      progress.value = String(Math.min(duration, Math.max(0, Number(s.position_ms) || 0)));
    }
    progress.disabled = duration <= 0;
  }
  if (playBtn) {
    playBtn.textContent = s.paused ? "▶" : "⏸";
    playBtn.setAttribute("aria-label", s.paused ? "Play" : "Pause");
  }
}

function spotifyEnsureUiState() {
  if (!window.__veraSpotifyUiState) {
    window.__veraSpotifyUiState = {
      view: "song",
      selectedPlaylistId: "",
      selectedPlaylistUri: "",
      selectedPlaylistName: ""
    };
  }
  return window.__veraSpotifyUiState;
}

function spotifySyncPlaylistSelectionHighlight(prefix) {
  const uiState = spotifyEnsureUiState();
  const playlistRoot = document.getElementById(`${prefix}-spotify-playlist-root`);
  if (!playlistRoot) return;
  const selId = String(uiState.selectedPlaylistId || "");
  playlistRoot.querySelectorAll(".spotify-playlist-row").forEach((el) => {
    if (!(el instanceof HTMLElement)) return;
    const id = String(el.dataset.playlistId || "");
    const selected = Boolean(selId && id === selId);
    el.classList.toggle("is-selected", selected);
    el.setAttribute("aria-selected", selected ? "true" : "false");
  });
}

function spotifyApplyViewMode(prefix) {
  const ui = spotifyEnsureUiState();
  const isPlaylist = ui.view === "playlist";
  const panelBody = document.querySelector(`[data-productivity-root="${prefix}"]`);
  const songView = document.getElementById(`${prefix}-spotify-song-view`);
  const playlistView = document.getElementById(`${prefix}-spotify-playlist-view`);
  const searchForm = document.getElementById(`${prefix}-spotify-search-form`);
  const songTab = document.getElementById(`${prefix}-spotify-tab-song`);
  const playlistTab = document.getElementById(`${prefix}-spotify-tab-playlist`);
  if (panelBody instanceof HTMLElement) {
    panelBody.dataset.spotifyView = isPlaylist ? "playlist" : "search";
  }
  if (songView) songView.hidden = isPlaylist;
  if (playlistView) playlistView.hidden = !isPlaylist;
  if (searchForm) {
    searchForm.hidden = isPlaylist;
    searchForm.setAttribute("aria-hidden", isPlaylist ? "true" : "false");
  }
  if (songTab) {
    songTab.classList.toggle("active", !isPlaylist);
    songTab.setAttribute("aria-selected", isPlaylist ? "false" : "true");
  }
  if (playlistTab) {
    playlistTab.classList.toggle("active", isPlaylist);
    playlistTab.setAttribute("aria-selected", isPlaylist ? "true" : "false");
  }
}

function openSpotifyConnectOAuth() {
  const u = new URL("/auth/spotify/login", `${localBackendBase()}/`);
  try {
    u.searchParams.set("opener_origin", window.location.origin);
  } catch (_) {
    /* ignore */
  }
  const w = window.open(u.href, "_blank");
  if (!w) {
    window.location.href = u.href;
    return;
  }
  const base = localBackendBase();
  clearInterval(window.__veraSpotifyOAuthPoll);
  const tick = async () => {
    if (w.closed) {
      clearInterval(window.__veraSpotifyOAuthPoll);
      window.__veraSpotifyOAuthPoll = null;
      void refreshSpotifyPanelAfterOAuthInOtherTab();
      return;
    }
    const st = await fetch(`${base}/api/spotify/connection-status`, {
      credentials: "include",
      headers: { ...veraSpotifyAuthHeaders() }
    })
      .then((r) => (r.ok ? r.json() : { connected: false }))
      .catch(() => ({ connected: false }));
    if (st.connected) {
      clearInterval(window.__veraSpotifyOAuthPoll);
      window.__veraSpotifyOAuthPoll = null;
      try {
        w.close();
      } catch (_) {
        /* ignore */
      }
      void refreshSpotifyPanelAfterOAuthInOtherTab();
    }
  };
  window.__veraSpotifyOAuthPoll = setInterval(tick, 1200);
  setTimeout(() => {
    if (window.__veraSpotifyOAuthPoll) {
      clearInterval(window.__veraSpotifyOAuthPoll);
      window.__veraSpotifyOAuthPoll = null;
    }
  }, 180000);
}

function wireSpotifyConnectLink(link) {
  if (!link || link.dataset.veraSpotifyConnectWired) return;
  link.dataset.veraSpotifyConnectWired = "1";
  link.href = "#";
  link.removeAttribute("target");
  link.removeAttribute("rel");
  link.addEventListener("click", (e) => {
    e.preventDefault();
    openSpotifyConnectOAuth();
  });
}

async function refreshSpotifyPanelAfterOAuthInOtherTab() {
  const prefix = appModePrefix();
  if (!document.getElementById(`${prefix}-spotify-connect-link`)) return;
  await refreshSpotifyConnectionUI(prefix);
  const st = await fetch(`${localBackendBase()}/api/spotify/connection-status`, {
    credentials: "include",
    headers: { ...veraSpotifyAuthHeaders() }
  })
    .then((r) => r.json())
    .catch(() => ({ connected: false }));
  if (st.connected) await ensureSpotifyWebPlayer(prefix);
}

async function waitForSpotifyDeviceId(maxMs = 20000) {
  const start = Date.now();
  while (Date.now() - start < maxMs) {
    if (window.__veraSpotifyDeviceId) return true;
    await new Promise((r) => setTimeout(r, 80));
  }
  return false;
}

async function ensureSpotifyWebPlayer(prefix) {
  const base = localBackendBase();
  if (window.__veraSpotifyPlayer && window.__veraSpotifyDeviceId) {
    // Rebind panel updates to the currently visible app (vera/bmo) when reusing the same Web Playback instance.
    const s = spotifyEnsureNowState();
    spotifyApplyNowStateToPanel(prefix);
    if (!s.paused && (Number(s.duration_ms) > 0 || String(s.title || "").trim())) {
      spotifyStartWebPlaybackUiTick(prefix);
    } else if (window.__veraSpotifyUiTickPrefix !== prefix) {
      window.__veraSpotifyUiTickPrefix = prefix;
    }
    return;
  }
  const tokRes = await fetch(`${base}/api/spotify/player-token`, {
    credentials: "include",
    headers: { ...veraSpotifyAuthHeaders() }
  });
  if (!tokRes.ok) return;
  await loadSpotifyWebSdkScript();
  const Spotify = window.Spotify;
  if (!Spotify) return;

  if (window.__veraSpotifyPlayer) {
    try {
      spotifyStopWebPlaybackUiTick();
      spotifyClearPendingSdkTrack();
      await window.__veraSpotifyPlayer.disconnect();
    } catch (_) {
      /* ignore */
    }
    window.__veraSpotifyPlayer = null;
    window.__veraSpotifyDeviceId = null;
  }

  const player = new Spotify.Player({
    name: "VERA Web",
    getOAuthToken: (cb) => {
      fetch(`${base}/api/spotify/player-token`, {
        credentials: "include",
        headers: { ...veraSpotifyAuthHeaders() }
      })
        .then((r) => (r.ok ? r.json() : Promise.reject()))
        .then((d) => cb(d.access_token))
        .catch(() => cb(""));
    },
    volume: spotifyGetVolume()
  });

  const readyPromise = new Promise((resolve, reject) => {
    const t = setTimeout(() => reject(new Error("Spotify Web Playback ready timeout")), 28000);
    player.addListener("ready", ({ device_id }) => {
      clearTimeout(t);
      window.__veraSpotifyDeviceId = device_id;
      window.__veraSpotifyPlayer = player;
      resolve(device_id);
    });
  });
  player.addListener("not_ready", () => {
    spotifyStopWebPlaybackUiTick();
    spotifyClearPendingSdkTrack();
    window.__veraSpotifyDeviceId = null;
  });
  player.addListener("authentication_error", ({ message }) => {
    console.warn("[Spotify] Web Playback authentication_error", message);
  });
  player.addListener("playback_error", ({ message }) => {
    console.warn("[Spotify] Web Playback playback_error", message);
  });
  player.addListener("player_state_changed", (state) => {
    if (!state) {
      spotifyStopWebPlaybackUiTick();
      return;
    }
    const curTrack = state?.track_window?.current_track;
    spotifySyncNowStateFromWebSdk(state);
    if (state.paused) removeSpotifyMiniButton(prefix);
    spotifyApplyNowStateToPanel(prefix);
    window.__veraSpotifyResumeWeb = {
      position_ms: Number(state.position) || 0,
      paused: !!state.paused
    };
    const playBtn = document.getElementById(`${prefix}-spotify-play`);
    if (playBtn) {
      if (!curTrack) {
        playBtn.textContent = "▶";
        playBtn.setAttribute("aria-label", "Play / pause");
      } else {
        playBtn.textContent = state.paused ? "▶" : "⏸";
        playBtn.setAttribute("aria-label", state.paused ? "Play" : "Pause");
      }
    }
    if (state && !state.paused && state.track_window?.current_track) {
      spotifyStartWebPlaybackUiTick(prefix);
    } else {
      spotifyStopWebPlaybackUiTick();
    }
  });

  const connected = await player.connect();
  if (!connected) {
    console.warn("[Spotify] player.connect returned false (Premium / browser restrictions?)");
    return;
  }
  try {
    await readyPromise;
  } catch (e) {
    console.warn("[Spotify]", e?.message || e);
  }
}

async function initSpotifyPlaybackForPanel(prefix) {
  wireSpotifyConnectLink(document.getElementById(`${prefix}-spotify-connect-link`));
  await refreshSpotifyConnectionUI(prefix);
  const st = await fetch(`${localBackendBase()}/api/spotify/connection-status`, {
    credentials: "include",
    headers: { ...veraSpotifyAuthHeaders() }
  })
    .then((r) => r.json())
    .catch(() => ({ connected: false }));
  if (st.connected) {
    await ensureSpotifyWebPlayer(prefix);
  }
}

function wireProductivityPanelEvents(prefix) {
  const uiState = spotifyEnsureUiState();
  const form = document.getElementById(`${prefix}-spotify-search-form`);
  const input = document.getElementById(`${prefix}-spotify-search-input`);
  const resultsEl = document.getElementById(`${prefix}-spotify-results`);
  const playlistRoot = document.getElementById(`${prefix}-spotify-playlist-root`);

  const applyPlaylistSelectedUi = () => {
    spotifySyncPlaylistSelectionHighlight(prefix);
  };
  applyPlaylistSelectedUi();

  document.getElementById(`${prefix}-spotify-tab-song`)?.addEventListener("click", () => {
    uiState.view = "song";
    spotifyApplyViewMode(prefix);
  });
  document.getElementById(`${prefix}-spotify-tab-playlist`)?.addEventListener("click", async () => {
    uiState.view = "playlist";
    spotifyApplyViewMode(prefix);
    if (!playlistRoot) return;
    if (playlistRoot.dataset.loaded === "1") return;
    playlistRoot.innerHTML = `<p class="spotify-results-hint">Loading playlists…</p>`;
    const fn = window.VeraSpotify?.getPlaylists;
    if (typeof fn !== "function") {
      playlistRoot.innerHTML = `<p class="spotify-results-error">Playlist API is unavailable.</p>`;
      return;
    }
    try {
      const list = await fn();
      renderSpotifyPlaylistResults(prefix, list);
      playlistRoot.dataset.loaded = "1";
    } catch (err) {
      playlistRoot.innerHTML = `<p class="spotify-results-error">${escapeHtml(String(err?.message ?? err))}</p>`;
    }
  });
  form?.addEventListener("submit", async (e) => {
    e.preventDefault();
    const q = String(input?.value || "").trim();
    if (!q || !resultsEl) return;
    resultsEl.innerHTML = `<p class="spotify-results-hint">Searching…</p>`;
    const fn = window.VeraSpotify?.searchTracks;
    if (typeof fn !== "function") {
      resultsEl.innerHTML = `<p class="spotify-results-hint">Set <code>window.VeraSpotify.searchTracks</code> to a function that returns Spotify results.</p>`;
      return;
    }
    try {
      const items = await fn(q);
      renderSpotifySearchResults(prefix, items);
      spotifyRememberSearchSnapshot(prefix);
    } catch (err) {
      resultsEl.innerHTML = `<p class="spotify-results-error">${escapeHtml(String(err?.message ?? err))}</p>`;
    }
  });

  document.getElementById(`${prefix}-spotify-results`)?.addEventListener("click", (e) => {
    const t = e.target;
    if (!(t instanceof HTMLElement)) return;
    const resultsRoot = document.getElementById(`${prefix}-spotify-results`);
    if (!resultsRoot || !resultsRoot.contains(t)) return;

    if (t.closest(".spotify-search-back")) {
      spotifyRestoreSearchSnapshot(prefix);
      return;
    }
    const albumPlay = t.closest(".spotify-album-play-triangle");
    if (albumPlay instanceof HTMLElement) {
      e.preventDefault();
      e.stopPropagation();
      const albumUri = albumPlay.dataset.spotifyAlbumUri || "";
      const detail = resultsRoot.querySelector(".spotify-search-detail");
      const ttl = detail?.querySelector(".spotify-search-detail-title")?.textContent || "Album";
      const sub = detail?.querySelector(".spotify-search-detail-sub")?.textContent || "";
      if (albumUri && window.VeraSpotify?.playPlaylist) {
        window.VeraSpotify
          .playPlaylist(albumUri, { playlist_name: ttl, context_subtitle: sub })
          .catch(() => {});
      }
      return;
    }
    const artistAlbumRow = t.closest(".spotify-artist-album-row");
    if (artistAlbumRow instanceof HTMLElement) {
      e.preventDefault();
      const albumUri = artistAlbumRow.dataset.spotifyAlbumUri || "";
      const title = artistAlbumRow.dataset.displayTitle || "";
      const sub = artistAlbumRow.dataset.displaySub || "";
      const thumbUrl = artistAlbumRow.dataset.thumbUrl || "";
      if (albumUri) {
        void spotifyOpenAlbumSearchDetail(prefix, { albumUri, title, sub, thumbUrl });
      }
      return;
    }
    const drow = t.closest(".spotify-detail-track-row");
    if (drow instanceof HTMLElement) {
      const uri = drow.dataset.spotifyUri || "";
      const previewUrl = drow.dataset.previewUrl || "";
      const openUrl = drow.dataset.openUrl || "";
      const title = drow.dataset.displayTitle || "";
      const artist = drow.dataset.displaySub || "";
      const titleEl = document.getElementById(`${prefix}-spotify-track-title`);
      const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
      if (titleEl) titleEl.textContent = title || "—";
      if (artistEl) artistEl.textContent = artist || "";
      const detailRoot = drow.closest(".spotify-search-detail");
      const coverImg = detailRoot?.querySelector(".spotify-search-detail-cover[src]");
      const ph = document.getElementById(`${prefix}-spotify-art-placeholder`);
      if (coverImg instanceof HTMLImageElement && coverImg.src && ph instanceof HTMLElement) {
        ph.style.backgroundImage = `url(${JSON.stringify(coverImg.src)})`;
        ph.style.backgroundSize = "cover";
      }
      const play = window.VeraSpotify?.playTrack;
      if (typeof play === "function" && uri) {
        play(uri, { title, artist, preview_url: previewUrl, open_url: openUrl }).catch(() => {});
      }
      return;
    }

    const row = t.closest(".spotify-result-row");
    if (!row || !(row instanceof HTMLElement) || row.closest(".spotify-search-detail")) return;
    const kind = String(row.dataset.spotifyKind || "track").toLowerCase();
    const uri = row.dataset.spotifyUri || "";
    const previewUrl = row.dataset.previewUrl || "";
    const openUrl = row.dataset.openUrl || "";
    const titleEl = document.getElementById(`${prefix}-spotify-track-title`);
    const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
    const title = row.dataset.displayTitle || row.querySelector(".spotify-result-title-text")?.textContent || "";
    const artist = row.dataset.displaySub || row.querySelector(".spotify-result-sub")?.textContent || "";
    if (kind === "album" && uri) {
      const thumbImg = row.querySelector("img.spotify-result-thumb");
      void spotifyOpenAlbumSearchDetail(prefix, {
        albumUri: uri,
        title,
        sub: artist,
        thumbUrl: thumbImg instanceof HTMLImageElement ? thumbImg.src || "" : ""
      });
      return;
    }
    if (kind === "artist" && uri) {
      const thumbImg = row.querySelector("img.spotify-result-thumb");
      void spotifyOpenArtistSearchDetail(prefix, {
        artistUri: uri,
        title,
        thumbUrl: thumbImg instanceof HTMLImageElement ? thumbImg.src || "" : ""
      });
      return;
    }
    if (titleEl) titleEl.textContent = title || "—";
    if (artistEl) artistEl.textContent = artist || "";
    const coverImg = row.querySelector("img.spotify-result-thumb");
    const ph = document.getElementById(`${prefix}-spotify-art-placeholder`);
    if (coverImg?.src && ph) {
      ph.style.backgroundImage = `url(${JSON.stringify(coverImg.src)})`;
      ph.style.backgroundSize = "cover";
    }
    const play = window.VeraSpotify?.playTrack;
    if (typeof play === "function" && uri) {
      play(uri, { title, artist, preview_url: previewUrl, open_url: openUrl }).catch(() => {});
    }
  });

  playlistRoot?.addEventListener("click", async (e) => {
    const t = e.target;
    if (!(t instanceof HTMLElement) || !playlistRoot.contains(t)) return;

    if (t.closest(".spotify-search-back")) {
      e.preventDefault();
      spotifyRestorePlaylistListSnapshot(prefix);
      return;
    }

    const albumPlay = t.closest(".spotify-album-play-triangle");
    if (albumPlay instanceof HTMLElement && albumPlay.closest(`#${prefix}-spotify-playlist-root`)) {
      e.preventDefault();
      e.stopPropagation();
      const uri = albumPlay.dataset.spotifyAlbumUri || "";
      const detail = playlistRoot.querySelector(".spotify-search-detail");
      const ttl = detail?.querySelector(".spotify-search-detail-title")?.textContent || "Playlist";
      const sub = detail?.querySelector(".spotify-search-detail-sub")?.textContent || "";
      if (uri && window.VeraSpotify?.playPlaylist) {
        window.VeraSpotify.playPlaylist(uri, { playlist_name: ttl, context_subtitle: sub }).catch(() => {});
      }
      return;
    }

    const drow = t.closest(".spotify-detail-track-row");
    if (drow instanceof HTMLElement && drow.closest(`[data-spotify-detail="playlist"]`)) {
      const uri = drow.dataset.spotifyUri || "";
      const previewUrl = drow.dataset.previewUrl || "";
      const openUrl = drow.dataset.openUrl || "";
      const title = drow.dataset.displayTitle || "";
      const artist = drow.dataset.displaySub || "";
      const titleEl = document.getElementById(`${prefix}-spotify-track-title`);
      const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
      if (titleEl) titleEl.textContent = title || "—";
      if (artistEl) artistEl.textContent = artist || "";
      const detailRoot = drow.closest(".spotify-search-detail");
      const coverImg = detailRoot?.querySelector(".spotify-search-detail-cover[src]");
      const ph = document.getElementById(`${prefix}-spotify-art-placeholder`);
      if (coverImg instanceof HTMLImageElement && coverImg.src && ph instanceof HTMLElement) {
        ph.style.backgroundImage = `url(${JSON.stringify(coverImg.src)})`;
        ph.style.backgroundSize = "cover";
      }
      const ctxUri = String(detailRoot?.dataset.spotifyPlaylistContextUri || uiState.selectedPlaylistUri || "").trim();
      const playFromPlaylist = window.VeraSpotify?.playPlaylistTrack;
      if (typeof playFromPlaylist === "function" && ctxUri && uri) {
        playFromPlaylist(ctxUri, uri, { title, artist, preview_url: previewUrl }).catch(() => {});
        return;
      }
      const play = window.VeraSpotify?.playTrack;
      if (typeof play === "function" && uri) {
        play(uri, { title, artist, preview_url: previewUrl, open_url: openUrl }).catch(() => {});
      }
      return;
    }

    const row = t.closest(".spotify-playlist-row");
    if (!(row instanceof HTMLElement)) return;
    const playlistId = row.dataset.playlistId || "";
    const playlistUri = row.dataset.playlistUri || "";
    const selectedName = row.querySelector(".spotify-result-title")?.textContent || "Playlist";
    const selectedSub = row.querySelector(".spotify-result-sub")?.textContent || "";
    uiState.selectedPlaylistId = playlistId;
    uiState.selectedPlaylistUri = playlistUri;
    uiState.selectedPlaylistName = selectedName;
    applyPlaylistSelectedUi();
    const thumbImg = row.querySelector("img.spotify-result-thumb");
    void spotifyOpenPlaylistSideDetail(prefix, {
      playlistId,
      playlistUri,
      title: selectedName,
      sub: selectedSub,
      thumbUrl: thumbImg instanceof HTMLImageElement ? thumbImg.src || "" : ""
    });
  });

  const playBtn = document.getElementById(`${prefix}-spotify-play`);
  playBtn?.addEventListener("click", () => {
    const toggle = window.VeraSpotify?.togglePlayback;
    if (typeof toggle === "function") toggle().catch(() => {});
  });

  document.getElementById(`${prefix}-spotify-logout`)?.addEventListener("click", async () => {
    const base = localBackendBase();
    await fetch(`${base}/api/spotify/logout`, {
      method: "POST",
      credentials: "include",
      headers: { ...veraSpotifyAuthHeaders(), "Content-Type": "application/json" }
    }).catch(() => {});
    clearVeraSpotifyBearer();
    try {
      await window.__veraSpotifyPlayer?.disconnect();
    } catch (_) {
      /* ignore */
    }
    window.__veraSpotifyPlayer = null;
    window.__veraSpotifyDeviceId = null;
    window.__veraSpotifyPlaybackActive = false;
    window.__veraSpotifyResume = null;
    window.__veraSpotifyResumeWeb = null;
    spotifyStopWebPlaybackUiTick();
    spotifyClearPendingSdkTrack();
    spotifyUpdateNowState({
      title: "",
      artist: "",
      cover_url: "",
      position_ms: 0,
      duration_ms: 0,
      paused: true,
      active: false
    });
    removeSpotifyMiniButton(prefix);
    await refreshSpotifyConnectionUI(prefix);
  });

  wireSpotifyConnectLink(document.getElementById(`${prefix}-spotify-connect-link`));

  const previewAudio = document.getElementById(`${prefix}-spotify-preview-audio`);
  if (previewAudio && !previewAudio.dataset.veraSpotifyPlayUiWired) {
    previewAudio.dataset.veraSpotifyPlayUiWired = "1";
    const onPreviewPlayState = () => {
      spotifySyncPlayButtonUi(prefix);
      window.__veraSpotifyPlaybackActive = !previewAudio.paused && previewAudio.currentTime > 0;
      if (!window.__veraSpotifyPlaybackActive) {
        removeSpotifyMiniButton(prefix);
      }
      if (previewAudio.ended) {
        window.__veraSpotifyResume = null;
      } else {
        persistSpotifyResumePreview(prefix);
      }
      spotifyUpdateNowState({
        position_ms: Math.round((previewAudio.currentTime || 0) * 1000),
        duration_ms: Number.isFinite(previewAudio.duration) ? Math.round(previewAudio.duration * 1000) : 0,
        paused: !!previewAudio.paused,
        active: !previewAudio.paused
      });
      spotifyApplyNowStateToPanel(prefix);
    };
    const onPreviewTime = () => {
      persistSpotifyResumePreview(prefix);
      spotifyUpdateNowState({
        position_ms: Math.round((previewAudio.currentTime || 0) * 1000),
        duration_ms: Number.isFinite(previewAudio.duration) ? Math.round(previewAudio.duration * 1000) : 0
      });
      spotifyApplyNowStateToPanel(prefix);
    };
    previewAudio.addEventListener("play", onPreviewPlayState);
    previewAudio.addEventListener("pause", onPreviewPlayState);
    previewAudio.addEventListener("ended", onPreviewPlayState);
    previewAudio.addEventListener("timeupdate", onPreviewTime);
    previewAudio.addEventListener("durationchange", onPreviewTime);
    previewAudio.addEventListener("loadedmetadata", onPreviewTime);
  }

  const progress = document.getElementById(`${prefix}-spotify-progress`);
  progress?.addEventListener("input", () => {
    const ms = Number(progress.value) || 0;
    const elapsed = document.getElementById(`${prefix}-spotify-time-elapsed`);
    if (elapsed) elapsed.textContent = spotifyFormatTimeMs(ms);
  });
  progress?.addEventListener("change", () => {
    const seekTo = window.VeraSpotify?.seekTo;
    const ms = Number(progress.value) || 0;
    if (typeof seekTo === "function") seekTo(ms).catch(() => {});
  });

  const volume = document.getElementById(`${prefix}-spotify-volume`);
  if (volume) {
    volume.value = String(Math.round(spotifyGetVolume() * 100));
    const onVolumeInput = () => {
      const setVolume = window.VeraSpotify?.setVolume;
      const value = (Number(volume.value) || 0) / 100;
      if (typeof setVolume === "function") setVolume(value).catch(() => {});
    };
    volume.addEventListener("input", onVolumeInput);
    volume.addEventListener("change", onVolumeInput);
  }

  void initSpotifyPlaybackForPanel(prefix).then(() => restoreSpotifyPlaybackAfterPanelRemount(prefix));
  spotifyApplyViewMode(prefix);
  spotifyApplyNowStateToPanel(prefix);
}

function renderProductivityPanel() {
  const sidePaneEl = uiEl("side-pane");
  if (!sidePaneEl) return;
  const prefix = appModePrefix();

  const mount = () => {
    sidePaneEl.hidden = false;
    sidePaneEl.dataset.sidePaneKind = "productivity";
    document.body.classList.add("news-panel-open");

    sidePaneEl.innerHTML = `
    <div class="side-pane-header">
      <div class="side-pane-heading">
        <h3 class="side-pane-title">Music panel</h3>
        <div class="side-pane-subtitle spotify-brand">Spotify</div>
      </div>
      <div class="side-pane-controls">
        <button class="side-pane-close" type="button" aria-label="Close panel">×</button>
      </div>
    </div>
    <div class="spotify-panel-body" data-productivity-root="${prefix}" data-spotify-view="search">
      <div class="spotify-connect-row" id="${prefix}-spotify-connect-row">
        <a class="spotify-connect-link" href="#" id="${prefix}-spotify-connect-link">Connect Spotify (Premium)</a>
        <button type="button" class="spotify-logout-btn" id="${prefix}-spotify-logout" hidden>Disconnect</button>
        <span class="spotify-connected-badge" id="${prefix}-spotify-connected-badge" hidden>Connected</span>
      </div>
      <div class="spotify-now-playing">
        <div class="spotify-art-placeholder" id="${prefix}-spotify-art-placeholder" aria-hidden="true"></div>
        <div class="spotify-track-meta">
          <div class="spotify-track-title" id="${prefix}-spotify-track-title">Nothing playing</div>
          <div class="spotify-track-artist" id="${prefix}-spotify-track-artist">Connect Spotify for in-browser playback, or use search + preview / Open in Spotify.</div>
          <div class="spotify-progress-wrap">
            <span class="spotify-time-text" id="${prefix}-spotify-time-elapsed">0:00</span>
            <input
              type="range"
              class="spotify-progress"
              id="${prefix}-spotify-progress"
              min="0"
              max="0"
              step="250"
              value="0"
              aria-label="Track position"
              disabled
            />
            <span class="spotify-time-text" id="${prefix}-spotify-time-total">0:00</span>
          </div>
        </div>
        <div class="spotify-transport">
          <button type="button" class="spotify-transport-btn" id="${prefix}-spotify-prev" aria-label="Previous" disabled title="Queue not implemented yet">⏮</button>
          <button type="button" class="spotify-transport-btn spotify-play-btn" id="${prefix}-spotify-play" aria-label="Play / pause">▶</button>
          <button type="button" class="spotify-transport-btn" id="${prefix}-spotify-next" aria-label="Next" disabled title="Queue not implemented yet">⏭</button>
          <div class="spotify-volume-wrap" title="Volume">
            <span class="spotify-volume-icon" aria-hidden="true">🔊</span>
            <input type="range" class="spotify-volume" id="${prefix}-spotify-volume" min="0" max="35" step="1" value="10" aria-label="Volume" />
          </div>
        </div>
      </div>
      <div class="spotify-view-toggle" role="tablist" aria-label="Search and playlists">
        <button type="button" class="spotify-view-tab active" id="${prefix}-spotify-tab-song" data-spotify-view="song" aria-selected="true">Search</button>
        <button type="button" class="spotify-view-tab" id="${prefix}-spotify-tab-playlist" data-spotify-view="playlist" aria-selected="false">Playlist</button>
      </div>
      <form class="spotify-search-form" id="${prefix}-spotify-search-form">
        <input type="search" class="spotify-search-input" id="${prefix}-spotify-search-input" placeholder="Search tracks, artists, albums…" autocomplete="off" />
        <button type="submit" class="spotify-search-submit">Search</button>
      </form>
      <div class="spotify-song-view" id="${prefix}-spotify-song-view">
        <div class="spotify-results" id="${prefix}-spotify-results" role="listbox" aria-label="Search results"></div>
      </div>
      <div class="spotify-playlist-view" id="${prefix}-spotify-playlist-view" hidden>
        <div
          class="spotify-results spotify-playlist-root"
          id="${prefix}-spotify-playlist-root"
          role="listbox"
          aria-label="Your playlists"
        >
          <p class="spotify-results-hint">Open this tab to load your playlists.</p>
        </div>
      </div>
      <audio id="${prefix}-spotify-preview-audio" preload="none" crossorigin="anonymous" hidden></audio>
    </div>
  `;

    sidePaneEl.scrollTop = 0;
    requestAnimationFrame(() => {
      sidePaneEl.classList.add("visible");
    });
    removeSpotifyMiniButton(prefix);
    wireProductivityPanelEvents(prefix);
  };

  runFlowModeSidePaneContentCrossfade(sidePaneEl, mount);
}

function toggleProductivityPanel() {
  const sidePaneEl = uiEl("side-pane");
  if (!sidePaneEl) return;
  const prefix = appModePrefix();
  const btn = document.getElementById(`${prefix}-productivity-mode`);
  if (sidePaneEl.hidden && sidePaneEl.dataset.sidePaneKind === "productivity" && sidePaneEl.innerHTML.trim()) {
    restoreProductivityPanel(prefix);
    return;
  }
  if (!sidePaneEl.hidden && sidePaneEl.dataset.sidePaneKind === "productivity") {
    hideSidePanel();
    return;
  }
  document.querySelectorAll(".productivity-mode-btn").forEach((b) => b.classList.remove("is-active"));
  renderProductivityPanel();
  btn?.classList.add("is-active");
}

function wireProductivityModeButtons() {
  document.getElementById("vera-productivity-mode")?.addEventListener("click", () => {
    toggleProductivityPanel();
  });
  document.getElementById("bmo-productivity-mode")?.addEventListener("click", () => {
    toggleProductivityPanel();
  });
}

wireProductivityModeButtons();

/* =========================
   WORK MODE — layout + reasoning stream + checklist
========================= */

const WORK_CHECKLIST_STORAGE_KEY = "vera_wm_checklist_v1";
const WORK_CHECKLIST_COMPLETED_COLLAPSED_KEY = "vera_wm_checklist_completed_collapsed_v1";
const VERA_TAB_ACTIVE_USER_KEY = "vera_active_user_tab_v1";
const WORK_LEFT_PANES_LAYOUT_KEY = "vera_wm_left_panes_layout_v1";
const REASONING_TABS_MAX = 3;
const REASONING_UNTITLED_TAB_NAME = "Untitled";
const REASONING_TABS_STATE_STORAGE_KEY_PREFIX = "vera_reasoning_tabs_state_v2";
const WORK_MODE_REASONING_LANES = [
  { idx: 0, label: "Thread 1 (atlas)" },
  { idx: 1, label: "Thread 2 (echo)" },
  { idx: 2, label: "Thread 3 (nova)" }
];
const WORK_MODE_STATE_TTL_MS = 60 * 60 * 1000; // 1 hour
const VERA_CHAT_STATE_STORAGE_KEY_PREFIX = "vera_chat_state_v1";
let chatStateHydrating = false;
let workChecklistSyncTimer = null;
let workChecklistHydrationPromise = null;
let workChecklistLocalMutationVersion = 0;

function markWorkChecklistLocalMutation() {
  workChecklistLocalMutationVersion += 1;
}

function readChecklistItemsFromStorage() {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY) || "[]";
    const parsed = JSON.parse(raw);
    return Array.isArray(parsed) ? parsed : [];
  } catch {
    return [];
  }
}

function queueWorkChecklistSyncToServer() {
  markWorkChecklistLocalMutation();
  if (workChecklistSyncTimer) window.clearTimeout(workChecklistSyncTimer);
  workChecklistSyncTimer = window.setTimeout(async () => {
    workChecklistSyncTimer = null;
    try {
      const items = readChecklistItemsFromStorage();
      const completedCollapsed = localStorage.getItem(WORK_CHECKLIST_COMPLETED_COLLAPSED_KEY) === "1";
      await fetch(authApiUrl("/api/work-mode/checklist"), {
        method: "PUT",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          session_id: getSessionId(),
          items,
          completed_collapsed: completedCollapsed
        })
      });
    } catch (_) {}
  }, 180);
}

async function hydrateWorkChecklistFromServer(force = false) {
  if (!force && workChecklistHydrationPromise) return workChecklistHydrationPromise;
  const startVersion = workChecklistLocalMutationVersion;
  workChecklistHydrationPromise = (async () => {
    try {
      const res = await fetch(
        `${authApiUrl("/api/work-mode/checklist")}?session_id=${encodeURIComponent(getSessionId())}`,
        { method: "GET" }
      );
      const data = await res.json().catch(() => ({}));
      if (!res.ok || !Array.isArray(data.items)) return;
      if (!force && startVersion !== workChecklistLocalMutationVersion) return;
      localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(data.items));
      if (typeof data.completed_collapsed === "boolean") {
        localStorage.setItem(
          WORK_CHECKLIST_COMPLETED_COLLAPSED_KEY,
          data.completed_collapsed ? "1" : "0"
        );
      }
      loadWorkChecklistItems();
    } catch (_) {
      /* keep local storage fallback */
    }
  })();
  await workChecklistHydrationPromise;
}

/** Same id source as `getSessionId()` for VERA — must never return "" or chat restore/save keys drift apart. */
function ensureVeraSessionIdForPersistence() {
  try {
    let id = getSessionScopedId(VERA_SESSION_STORAGE_KEY);
    if (!id) {
      id = crypto.randomUUID();
      setSessionScopedId(VERA_SESSION_STORAGE_KEY, id);
    }
    return id;
  } catch (_) {
    return "";
  }
}

function getVeraChatStateStorageKey() {
  const id = ensureVeraSessionIdForPersistence();
  if (!id) return `${VERA_CHAT_STATE_STORAGE_KEY_PREFIX}:unknown`;
  return `${VERA_CHAT_STATE_STORAGE_KEY_PREFIX}:${id}`;
}

function migrateLegacyVeraChatStorageKey() {
  try {
    const id = ensureVeraSessionIdForPersistence();
    const modern = `${VERA_CHAT_STATE_STORAGE_KEY_PREFIX}:${id}`;
    /* Older builds used an empty session segment when the id had not been created yet. */
    const legacy = `${VERA_CHAT_STATE_STORAGE_KEY_PREFIX}:`;
    const raw = localStorage.getItem(legacy);
    if (raw && !localStorage.getItem(modern)) {
      localStorage.setItem(modern, raw);
    }
  } catch (_) {}
}

function persistVeraClientStateOnUnload() {
  persistVeraChatState();
  persistReasoningTabsState();
}

function persistVeraChatState() {
  if (chatStateHydrating) return;
  const convo = document.getElementById("vera-conversation");
  if (!convo) return;
  const messages = [];
  for (const row of convo.querySelectorAll(".message-row")) {
    const who = row.classList.contains("user") ? "user" : row.classList.contains("vera") ? "vera" : "";
    if (!who) continue;
    const bubble = row.querySelector(".bubble");
    if (!(bubble instanceof HTMLElement)) continue;
    if (bubble.classList.contains("interrupt-preview")) continue;
    const text = String(bubble.textContent || "").trim();
    if (!text) continue;
    messages.push({ who, text });
  }
  const payload = { ts: Date.now(), messages };
  try {
    localStorage.setItem(getVeraChatStateStorageKey(), JSON.stringify(payload));
  } catch (_) {}
}

function restoreVeraChatState() {
  const convo = document.getElementById("vera-conversation");
  if (!convo) return;
  let raw = "";
  try {
    raw = localStorage.getItem(getVeraChatStateStorageKey()) || "";
  } catch (_) {
    return;
  }
  if (!raw) return;
  let parsed;
  try {
    parsed = JSON.parse(raw);
  } catch (_) {
    return;
  }
  const ts = Number(parsed?.ts) || 0;
  if (!ts || Date.now() - ts > WORK_MODE_STATE_TTL_MS) {
    try {
      localStorage.removeItem(getVeraChatStateStorageKey());
    } catch (_) {}
    return;
  }
  const messages = Array.isArray(parsed?.messages) ? parsed.messages : [];
  if (!messages.length) return;
  chatStateHydrating = true;
  try {
    convo.replaceChildren();
    messages.forEach((m) => {
      const who = m?.who === "user" ? "user" : "vera";
      const text = String(m?.text || "").trim();
      if (text) addBubble(text, who, { path: "restore-chat-state" });
    });
    if (convo.children.length > 0) ensureChatStartedLayout();
  } finally {
    chatStateHydrating = false;
  }
}

function getReasoningTabsStateStorageKey() {
  return `${REASONING_TABS_STATE_STORAGE_KEY_PREFIX}:${getSessionId()}`;
}

function getWorkModeReasoningLaneLabel(idx) {
  const lane = WORK_MODE_REASONING_LANES.find((x) => x.idx === Number(idx));
  return lane?.label || `Thread ${Number(idx) + 1}`;
}

function getWorkModeReasoningLaneId(idx) {
  if (Number(idx) === 0) return "atlas";
  if (Number(idx) === 1) return "echo";
  if (Number(idx) === 2) return "nova";
  return "atlas";
}

function createReasoningLanePanel(idx, html = "", isActive = false) {
  const panel = document.createElement("div");
  panel.className = "vera-reasoning-tab-panel";
  if (isActive) panel.classList.add("is-active");
  panel.dataset.tabIndex = String(idx);
  panel.dataset.tabTopic = REASONING_UNTITLED_TAB_NAME;
  panel.dataset.tabTopicSet = "0";
  panel.dataset.laneLabel = getWorkModeReasoningLaneLabel(idx);
  panel.id = `vera-reasoning-tab-panel-${idx}`;
  panel.setAttribute("role", "tabpanel");
  panel.setAttribute("aria-label", `Reasoning lane ${idx + 1}`);
  const scroll = document.createElement("div");
  scroll.className = "vera-reasoning-scroll vera-reasoning-md-panel";
  if (idx === 0) scroll.id = "vera-reasoning-md";
  scroll.setAttribute("aria-live", "polite");
  scroll.innerHTML = String(html || "");
  panel.appendChild(scroll);
  return panel;
}

function ensureFixedReasoningLanePanels(savedByIdx = new Map(), activeIdx = 0) {
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  if (!panelsRoot) return;
  panelsRoot.replaceChildren();
  WORK_MODE_REASONING_LANES.forEach((lane, i) => {
    const saved = savedByIdx.get(lane.idx) || {};
    const panel = createReasoningLanePanel(
      lane.idx,
      saved.html || "",
      Number(activeIdx) === lane.idx || (i === 0 && activeIdx == null)
    );
    panelsRoot.appendChild(panel);
  });
}

function getReasoningScrollElByLane(index) {
  const panel = document.querySelector(
    `#vera-reasoning-tab-panels .vera-reasoning-tab-panel[data-tab-index="${Number(index)}"]`
  );
  return panel?.querySelector(".vera-reasoning-md-panel") || null;
}

/** Snapshot reasoning tabs to localStorage — call only on page unload (see wireReasoningTabStrip). */
function persistReasoningTabsState() {
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  if (!panelsRoot) return;
  const panels = [...panelsRoot.querySelectorAll(".vera-reasoning-tab-panel")];
  const payload = {
    ts: Date.now(),
    tabs: panels.map((p) => ({
      idx: Number(p.dataset.tabIndex) || 0,
      topic: String(p.dataset.tabTopic || REASONING_UNTITLED_TAB_NAME),
      topicSet: String(p.dataset.tabTopicSet || "0"),
      active: p.classList.contains("is-active"),
      html: (p.querySelector(".vera-reasoning-md-panel") || p.querySelector(".vera-reasoning-scroll"))?.innerHTML || ""
    }))
  };
  try {
    localStorage.setItem(getReasoningTabsStateStorageKey(), JSON.stringify(payload));
  } catch (_) {}
}

function restoreReasoningTabsState() {
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  if (!panelsRoot) return;
  let raw = "";
  try {
    raw = localStorage.getItem(getReasoningTabsStateStorageKey()) || "";
  } catch (_) {
    return;
  }
  if (!raw) {
    ensureFixedReasoningLanePanels(new Map(), 0);
    return;
  }
  let parsed;
  try {
    parsed = JSON.parse(raw);
  } catch (_) {
    return;
  }
  const tabs = Array.isArray(parsed?.tabs) ? parsed.tabs.slice(0, REASONING_TABS_MAX) : [];
  if (!tabs.length) {
    ensureFixedReasoningLanePanels(new Map(), 0);
    return;
  }
  const ts = Number(parsed?.ts) || 0;
  if (!ts || Date.now() - ts > WORK_MODE_STATE_TTL_MS) {
    try {
      localStorage.removeItem(getReasoningTabsStateStorageKey());
    } catch (_) {}
    ensureFixedReasoningLanePanels(new Map(), 0);
    return;
  }
  const savedByIdx = new Map();
  let activeIdx = 0;
  tabs.forEach((t) => {
    const idx = Number(t?.idx);
    if (!Number.isFinite(idx)) return;
    if (Boolean(t?.active)) activeIdx = idx;
    savedByIdx.set(idx, { html: String(t?.html || "") });
  });
  ensureFixedReasoningLanePanels(savedByIdx, activeIdx);
}

function getActiveReasoningScrollEl() {
  const p = document.querySelector("#vera-reasoning-tab-panels .vera-reasoning-tab-panel.is-active .vera-reasoning-md-panel");
  if (p) return p;
  return document.getElementById("vera-reasoning-md");
}

/** Each assistant reasoning run appends a new block inside the active space (scroll container). */
function appendReasoningTurnMount(scrollEl) {
  let el = scrollEl;
  if (!el) {
    el = document.getElementById("vera-reasoning-md");
    if (!el) return null;
  }
  if (el.querySelector(".vera-reasoning-turn")) {
    const sep = document.createElement("div");
    sep.className = "vera-reasoning-turn-sep";
    const hr = document.createElement("hr");
    hr.className = "vera-reasoning-turn-hr";
    hr.setAttribute("aria-hidden", "true");
    sep.appendChild(hr);
    el.appendChild(sep);
  }
  const turn = document.createElement("div");
  turn.className = "vera-reasoning-turn";
  el.appendChild(turn);
  return turn;
}

function getReasoningTabTopicLabel(panel) {
  const laneLabel = String(panel?.dataset?.laneLabel || "").trim();
  if (laneLabel) return laneLabel;
  const topic = String(panel?.dataset?.tabTopic || "").trim();
  return topic || REASONING_UNTITLED_TAB_NAME;
}

function toTitleCaseWord(w) {
  if (!w) return "";
  if (/^[A-Z0-9]{2,}$/.test(w)) return w;
  return w.charAt(0).toUpperCase() + w.slice(1).toLowerCase();
}

/** Skip headings / tab titles that are generic assistant filler, not the task topic. */
function isBanalReasoningTopicLabel(s) {
  const t = String(s || "")
    .toLowerCase()
    .replace(/[—–-]+/g, " ")
    .replace(/\s+/g, " ")
    .trim();
  if (!t) return true;
  if (/^(yes|yeah|yep|sure|ok|okay|absolutely)\b/.test(t)) return true;
  if (/\b(i can help|i'll help|i will help|happy to help|let me help|here to help)\b/.test(t)) return true;
  if (/\b(work through it|help you work|walk you through)\b/.test(t) && t.split(/\s+/).length <= 8) return true;
  return false;
}

function compactTopicPhrase(text, maxWords = 4) {
  const raw = String(text || "")
    .replace(/[`*_#>[\]()]/g, " ")
    .replace(/\s+/g, " ")
    .trim();
  if (!raw) return "";
  const withoutLead = raw
    .replace(/^(here(?:'s| is)\s+)?(?:an?\s+)?(?:short\s+)?example(?:\s+of)?[:\-\s]*/i, "")
    .trim();
  const candidate = withoutLead || raw;
  const words = candidate.match(/[A-Za-z0-9][A-Za-z0-9'+-]*/g) || [];
  if (!words.length) return "";
  const badEdge = new Set([
    "a", "an", "the", "is", "are", "was", "were", "be", "being", "been", "to", "of", "and", "or",
    "for", "with", "in", "on", "at", "from", "by", "as", "that", "this"
  ]);
  let start = 0;
  let end = words.length;
  while (start < end && badEdge.has(words[start].toLowerCase())) start += 1;
  while (end > start && badEdge.has(words[end - 1].toLowerCase())) end -= 1;
  const core = words.slice(start, end).slice(0, maxWords);
  if (!core.length) return "";
  const out = core.map((w) => toTitleCaseWord(w)).join(" ");
  if (isBanalReasoningTopicLabel(out)) return "";
  return out;
}

function keywordTopicFromText(text, maxWords = 4) {
  const tokens = (String(text || "").toLowerCase().match(/[a-z][a-z0-9'+-]*/g) || []);
  if (!tokens.length) return "";
  const stop = new Set([
    "the", "and", "for", "with", "that", "this", "from", "into", "your", "you", "show", "example",
    "short", "here", "there", "what", "when", "where", "which", "about", "have", "has", "had", "can",
    "could", "would", "should", "step", "steps", "then", "than", "just", "more", "most", "some", "any",
    "using", "use", "used", "also", "very", "much", "into", "onto", "over", "under",
    "yes", "yeah", "yep", "sure", "help", "i'll", "okay", "ok"
  ]);
  const counts = new Map();
  const firstPos = new Map();
  tokens.forEach((t, i) => {
    if (t.length < 3 || stop.has(t)) return;
    if (!firstPos.has(t)) firstPos.set(t, i);
    counts.set(t, (counts.get(t) || 0) + 1);
  });
  const ranked = [...counts.entries()]
    .sort((a, b) => (b[1] - a[1]) || ((firstPos.get(a[0]) || 0) - (firstPos.get(b[0]) || 0)))
    .slice(0, maxWords)
    .map(([t]) => toTitleCaseWord(t));
  return ranked.join(" ");
}

function buildReasoningTopicLabel({ summaryText = "", markdownText = "", userPrompt = "" } = {}) {
  const headingLines = String(markdownText || "")
    .split("\n")
    .map((line) => line.trim())
    .filter((line) => /^#{1,6}\s+/.test(line))
    .map((line) => line.replace(/^#{1,6}\s+/, "").trim());
  for (const h of headingLines) {
    if (isBanalReasoningTopicLabel(h)) continue;
    const t = compactTopicPhrase(h, 4);
    if (t) return t;
  }
  const keywordTopic = keywordTopicFromText(`${summaryText}\n${markdownText}`, 4);
  if (keywordTopic && !isBanalReasoningTopicLabel(keywordTopic)) return keywordTopic;
  const summaryTopic = compactTopicPhrase(summaryText, 4);
  if (summaryTopic && !isBanalReasoningTopicLabel(summaryTopic)) return summaryTopic;
  const promptTopic = compactTopicPhrase(userPrompt, 4);
  if (promptTopic && !isBanalReasoningTopicLabel(promptTopic)) return promptTopic;
  return "";
}

function setReasoningTabTopicFromFinal(turnEl, opts = {}) {
  if (!turnEl) return;
  const panel = turnEl.closest(".vera-reasoning-tab-panel");
  if (!panel) return;
  if (String(panel.dataset.laneLabel || "").trim()) return;
  if (String(panel.dataset.tabTopicSet || "") === "1") return;
  const topic = buildReasoningTopicLabel(opts);
  panel.dataset.tabTopic = topic || REASONING_UNTITLED_TAB_NAME;
  panel.dataset.tabTopicSet = "1";
  renderReasoningTabStrip();
}

function renderReasoningTabStrip() {
  const tabsEl = document.getElementById("vera-reasoning-tabs");
  const addBtn = document.getElementById("vera-reasoning-tab-add");
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  if (!tabsEl || !panelsRoot) return;
  const panels = [...panelsRoot.querySelectorAll(".vera-reasoning-tab-panel")];
  tabsEl.replaceChildren();
  panels.forEach((panel, i) => {
    const idx = Number(panel.dataset.tabIndex);
    const slot = document.createElement("div");
    slot.className =
      "vera-reasoning-tab-slot" + (panel.classList.contains("is-active") ? " is-active" : "");
    const tabBtn = document.createElement("button");
    tabBtn.type = "button";
    tabBtn.className = "vera-reasoning-tab";
    tabBtn.setAttribute("role", "tab");
    tabBtn.setAttribute("aria-selected", panel.classList.contains("is-active") ? "true" : "false");
    tabBtn.dataset.tabIndex = String(idx);
    const tabLabel = getReasoningTabTopicLabel(panel);
    tabBtn.title = tabLabel;
    const label = document.createElement("span");
    label.className = "vera-reasoning-tab-label";
    label.textContent = tabLabel;
    tabBtn.appendChild(label);
    slot.appendChild(tabBtn);
    tabsEl.appendChild(slot);
  });
  if (addBtn) addBtn.hidden = true;
}

function activateReasoningTab(index) {
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  if (!panelsRoot) return;
  panelsRoot.querySelectorAll(".vera-reasoning-tab-panel").forEach((p) => {
    p.classList.toggle("is-active", Number(p.dataset.tabIndex) === index);
  });
  renderReasoningTabStrip();
  syncWorkModeReasoningCancelButton();
}

function addReasoningTab() {
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  if (!panelsRoot) return;
  const panels = [...panelsRoot.querySelectorAll(".vera-reasoning-tab-panel")];
  if (panels.length >= REASONING_TABS_MAX) return;
  const maxIdx = panels.reduce((m, p) => Math.max(m, Number(p.dataset.tabIndex) || 0), -1);
  const idx = maxIdx + 1;
  const panel = document.createElement("div");
  panel.className = "vera-reasoning-tab-panel";
  panel.dataset.tabIndex = String(idx);
  panel.dataset.tabTopic = REASONING_UNTITLED_TAB_NAME;
  panel.dataset.tabTopicSet = "0";
  panel.id = `vera-reasoning-tab-panel-${idx}`;
  panel.setAttribute("role", "tabpanel");
  panel.setAttribute("aria-label", `Reasoning space ${panels.length + 1}`);
  const scroll = document.createElement("div");
  scroll.className = "vera-reasoning-scroll vera-reasoning-md-panel";
  scroll.setAttribute("aria-live", "polite");
  panel.appendChild(scroll);
  panels.forEach((p) => p.classList.remove("is-active"));
  panelsRoot.appendChild(panel);
  panel.classList.add("is-active");
  renderReasoningTabStrip();
}

function closeReasoningTab(index) {
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  if (!panelsRoot) return;
  const panels = [...panelsRoot.querySelectorAll(".vera-reasoning-tab-panel")];
  if (panels.length <= 1) return;
  const victim = panels.find((p) => Number(p.dataset.tabIndex) === index);
  if (!victim) return;
  const wasActive = victim.classList.contains("is-active");
  victim.remove();
  if (wasActive) {
    const rest = [...panelsRoot.querySelectorAll(".vera-reasoning-tab-panel")];
    rest[0]?.classList.add("is-active");
  }
  renderReasoningTabStrip();
}

function wireReasoningTabStrip() {
  const tabsEl = document.getElementById("vera-reasoning-tabs");
  const addBtn = document.getElementById("vera-reasoning-tab-add");
  if (!tabsEl || tabsEl.dataset.wiredReasoningTabs === "1") return;
  if (!document.getElementById("vera-reasoning-tab-panels")) return;
  const panelsRoot = document.getElementById("vera-reasoning-tab-panels");
  restoreReasoningTabsState();
  if (panelsRoot.querySelectorAll(".vera-reasoning-tab-panel").length !== REASONING_TABS_MAX) {
    ensureFixedReasoningLanePanels(new Map(), 0);
  }
  panelsRoot?.querySelectorAll(".vera-reasoning-tab-panel").forEach((panel) => {
    if (!String(panel.dataset.laneLabel || "").trim()) {
      panel.dataset.laneLabel = getWorkModeReasoningLaneLabel(Number(panel.dataset.tabIndex || "0"));
    }
    if (!String(panel.dataset.tabTopic || "").trim()) {
      panel.dataset.tabTopic = REASONING_UNTITLED_TAB_NAME;
    }
    if (!String(panel.dataset.tabTopicSet || "").trim()) {
      panel.dataset.tabTopicSet = "0";
    }
  });
  tabsEl.dataset.wiredReasoningTabs = "1";
  tabsEl.addEventListener("click", (e) => {
    const tab = e.target.closest("button.vera-reasoning-tab");
    if (tab && tab.dataset.tabIndex != null) {
      activateReasoningTab(Number(tab.dataset.tabIndex));
    }
  });
  if (addBtn) addBtn.hidden = true;
  renderReasoningTabStrip();
  if (window.__veraReasoningTabsUnloadHook !== "1") {
    window.__veraReasoningTabsUnloadHook = "1";
    window.addEventListener("beforeunload", persistVeraClientStateOnUnload);
    window.addEventListener("pagehide", persistVeraClientStateOnUnload);
  }
}

function getWorkModeLeftPaneLayout() {
  try {
    const v = localStorage.getItem(WORK_LEFT_PANES_LAYOUT_KEY);
    if (v === "music-full" || v === "checklist-full" || v === "split") return v;
  } catch (_) {}
  return "split";
}

function setWorkModeLeftPaneLayout(layout) {
  const left = document.getElementById("vera-wm-left");
  if (!left) return;
  if (layout !== "split" && layout !== "music-full" && layout !== "checklist-full") layout = "split";
  left.dataset.wmLeftLayout = layout;
  try {
    localStorage.setItem(WORK_LEFT_PANES_LAYOUT_KEY, layout);
  } catch (_) {}
}

function applyWorkModeLeftPaneLayoutFromStorage() {
  setWorkModeLeftPaneLayout(getWorkModeLeftPaneLayout());
}

function wireWorkModeLeftPaneLayout() {
  const left = document.getElementById("vera-wm-left");
  if (!left || left.dataset.wmLeftPaneWired === "1") return;
  left.dataset.wmLeftPaneWired = "1";
  left.addEventListener("click", (e) => {
    if (!isVeraWorkModeOn()) return;
    const btn = e.target.closest("[data-wm-pane-action]");
    if (!(btn instanceof HTMLElement)) return;
    const pane = btn.dataset.wmPane;
    const action = btn.dataset.wmPaneAction;
    if ((pane !== "music" && pane !== "checklist") || (action !== "expand" && action !== "collapse")) return;
    e.preventDefault();
    const cur = getWorkModeLeftPaneLayout();

    if (action === "collapse") {
      if (cur === "split") setWorkModeLeftPaneLayout(pane === "music" ? "checklist-full" : "music-full");
      else if (cur === "music-full" && pane === "music") setWorkModeLeftPaneLayout("split");
      else if (cur === "checklist-full" && pane === "checklist") setWorkModeLeftPaneLayout("split");
      return;
    }
    if (action === "expand") {
      if (cur === "split") setWorkModeLeftPaneLayout(pane === "music" ? "music-full" : "checklist-full");
      else if (cur === "music-full" && pane === "checklist") setWorkModeLeftPaneLayout("split");
      else if (cur === "checklist-full" && pane === "music") setWorkModeLeftPaneLayout("split");
    }
  });
}
let workModeReasoningConfirmPending = null;
let workModeReasoningAttachment = null;
const workModeReasoningLaneBusy = new Map(WORK_MODE_REASONING_LANES.map((lane) => [lane.idx, false]));
const workModeReasoningLaneWaitQueue = [];
const workModeReasoningAbortControllers = new Map();
const workModeTypedTurnQueue = [];
const WORK_MODE_TYPED_TURN_QUEUE_MAX = 3;
let workModeTypedQueueDraining = false;

function syncWorkModeReasoningCancelButton() {
  const btn = document.getElementById("vera-reasoning-cancel");
  if (!btn) return;
  const activeIdx = getActiveReasoningLaneIndex();
  btn.hidden = activeIdx == null || !workModeReasoningAbortControllers.has(Number(activeIdx));
}

function getActiveReasoningLaneIndex() {
  const panel = document.querySelector("#vera-reasoning-tab-panels .vera-reasoning-tab-panel.is-active");
  if (!(panel instanceof HTMLElement)) return null;
  const idx = Number(panel.dataset.tabIndex);
  return Number.isFinite(idx) ? idx : null;
}

function cancelWorkModeReasoningLane(idx) {
  const laneIdx = Number(idx);
  const ctl = workModeReasoningAbortControllers.get(laneIdx);
  if (!ctl) return false;
  try {
    ctl.abort();
  } catch (_) {}
  setWorkModeAttachmentMeta(`Reasoning cancelled for ${getWorkModeReasoningLaneLabel(laneIdx)}.`);
  return true;
}

function endWorkModeReasoningLaneRun(idx) {
  workModeReasoningAbortControllers.delete(Number(idx));
  releaseWorkModeReasoningLane(idx);
  syncWorkModeReasoningCancelButton();
}

function acquireWorkModeReasoningLane() {
  const idleLane = WORK_MODE_REASONING_LANES.find((lane) => !workModeReasoningLaneBusy.get(lane.idx));
  if (idleLane) {
    workModeReasoningLaneBusy.set(idleLane.idx, true);
    syncWorkModeReasoningCancelButton();
    return Promise.resolve(idleLane.idx);
  }
  return new Promise((resolve) => {
    workModeReasoningLaneWaitQueue.push(resolve);
  });
}

function releaseWorkModeReasoningLane(idx) {
  const laneIdx = Number(idx);
  const next = workModeReasoningLaneWaitQueue.shift();
  if (typeof next === "function") {
    workModeReasoningLaneBusy.set(laneIdx, true);
    syncWorkModeReasoningCancelButton();
    next(laneIdx);
    return;
  }
  workModeReasoningLaneBusy.set(laneIdx, false);
  syncWorkModeReasoningCancelButton();
}

function enqueueWorkModeTypedTurn(text, opts = {}) {
  if (workModeTypedTurnQueue.length >= WORK_MODE_TYPED_TURN_QUEUE_MAX) {
    console.warn("[WorkMode] typed queue full; dropping new request", {
      max: WORK_MODE_TYPED_TURN_QUEUE_MAX
    });
    return false;
  }
  workModeTypedTurnQueue.push({
    text: String(text || ""),
    opts: { ...opts, __fromQueue: true }
  });
  return true;
}

function isWorkModeTypedTurnBlocked() {
  /* Work-mode typed should not barge-in TTS; only block on active request. */
  return requestInFlight;
}

async function drainWorkModeTypedTurnQueue() {
  if (workModeTypedQueueDraining) return;
  if (!isVeraWorkModeOn() || appModePrefix() !== "vera") return;
  workModeTypedQueueDraining = true;
  try {
    while (workModeTypedTurnQueue.length > 0) {
      if (isWorkModeTypedTurnBlocked()) break;
      const next = workModeTypedTurnQueue.shift();
      if (!next?.text) continue;
      await sendVeraWorkModeTypedInferTurn(next.text, next.opts || {});
    }
  } finally {
    workModeTypedQueueDraining = false;
  }
}

function scheduleWorkModeTypedQueueDrain() {
  window.setTimeout(() => {
    void drainWorkModeTypedTurnQueue();
  }, 0);
}

window.clearWorkModeReasoningPending = function clearWorkModeReasoningPending() {
  workModeReasoningConfirmPending = null;
};

function isVeraWorkModeOn() {
  return Boolean(document.getElementById("vera-app")?.classList.contains("work-mode"));
}

window.layoutVeraWorkModePanels = function layoutVeraWorkModePanels(on) {
  const pane = document.getElementById("vera-side-pane");
  const musicBody = document.getElementById("vera-wm-music-body");
  const chatMain = document.querySelector("#vera-app .chat-main");
  if (!pane || !musicBody || !chatMain) return;
  try {
    if (on) {
      if (pane.parentElement !== musicBody) musicBody.appendChild(pane);
      const hasProductivityMarkup =
        Boolean(pane.innerHTML.trim()) && pane.dataset.sidePaneKind === "productivity";
      if (!hasProductivityMarkup) {
        renderProductivityPanel();
      } else if (pane.hidden) {
        restoreProductivityPanel("vera");
      }
      applyWorkModeLeftPaneLayoutFromStorage();
    } else if (pane.parentElement !== chatMain) {
      chatMain.appendChild(pane);
    }
  } catch (e) {
    console.warn("[WorkMode] layout panes", e);
  }
};

window.ensureWorkModeVoiceUiActive = async function ensureWorkModeVoiceUiActive() {
  try {
    if (window.matchMedia("(max-width: 768px)").matches) return;
    if (appModePrefix() !== "vera") return;
    listeningMode = "continuous";
    inputMuted = false;
    updateMuteInputButton();
    await initMic();
    micStream?.getAudioTracks().forEach((track) => {
      track.enabled = true;
    });
    listening = true;
    if (!processing && getAudioEl()?.paused) {
      startListening();
    }
  } catch (e) {
    console.warn("[WorkMode] ensure voice UI active", e);
  }
};
window.ensureVeraVoiceUiActive = window.ensureWorkModeVoiceUiActive;

function escapeHtml(s) {
  return String(s)
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;");
}

function renderWorkModeMarkdown(el, markdown, summaryText = "") {
  if (!el) return;
  const lines = String(markdown || "").replace(/\r/g, "").split("\n");
  const renderMath = (src, displayMode) => {
    try {
      if (window.katex && typeof window.katex.renderToString === "function") {
        return window.katex.renderToString(src, { throwOnError: false, displayMode });
      }
    } catch {}
    return null;
  };
  const applyInlineMath = (escapedHtml) => {
    const withDisplayMath = escapedHtml
      .replace(
        /\\\[(.+?)\\\]/g,
        (_, expr) => renderMath(expr, true) || `\\[${expr}\\]`
      )
      .replace(
        /\$\$(.+?)\$\$/g,
        (_, expr) => renderMath(expr, true) || `$$${expr}$$`
      );
    const withParenMath = withDisplayMath.replace(
      /\\\((.+?)\\\)/g,
      (_, expr) => renderMath(expr, false) || `\\(${expr}\\)`
    );
    return withParenMath.replace(
      /\$(?!\s)(.+?)(?<!\s)\$/g,
      (_, expr) => renderMath(expr, false) || `$${expr}$`
    );
  };
  const inline = (text) => {
    let t = escapeHtml(text);
    t = t.replace(/`([^`]+)`/g, "<code>$1</code>");
    t = t.replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>");
    t = t.replace(/\*([^*]+)\*/g, "<em>$1</em>");
    return applyInlineMath(t);
  };

  // Keep summaryText for voice/history plumbing, but do not render it in the reasoning panel UI.
  let html = "";
  let inCode = false;
  let listType = "";
  let para = [];
  const flushPara = () => {
    if (para.length) {
      html += `<p>${inline(para.join(" "))}</p>`;
      para = [];
    }
  };
  const closeList = () => {
    if (listType) {
      html += listType === "ol" ? "</ol>" : "</ul>";
      listType = "";
    }
  };

  for (const raw of lines) {
    const line = raw ?? "";
    if (line.trimStart().startsWith("```")) {
      flushPara();
      closeList();
      if (!inCode) {
        inCode = true;
        html += "<pre><code>";
      } else {
        inCode = false;
        html += "</code></pre>";
      }
      continue;
    }
    if (inCode) {
      html += `${escapeHtml(line)}\n`;
      continue;
    }
    const dispDollar = line.match(/^\s*\$\$(.+?)\$\$\s*$/);
    if (dispDollar) {
      flushPara();
      closeList();
      const block = renderMath(dispDollar[1], true);
      html += block || `<pre><code>${escapeHtml(dispDollar[1])}</code></pre>`;
      continue;
    }
    const dispBracket = line.match(/^\s*\\\[(.+?)\\\]\s*$/);
    if (dispBracket) {
      flushPara();
      closeList();
      const block = renderMath(dispBracket[1], true);
      html += block || `<pre><code>${escapeHtml(dispBracket[1])}</code></pre>`;
      continue;
    }
    const h = line.match(/^\s{0,3}(#{1,6})\s+(.*)$/);
    if (h) {
      flushPara();
      closeList();
      const lvl = h[1].length;
      html += `<h${lvl}>${inline(h[2].trim())}</h${lvl}>`;
      continue;
    }
    const ol = line.match(/^\s*\d+\.\s+(.*)$/);
    if (ol) {
      flushPara();
      if (listType && listType !== "ol") closeList();
      if (!listType) {
        listType = "ol";
        html += "<ol>";
      }
      html += `<li>${inline(ol[1])}</li>`;
      continue;
    }
    const ul = line.match(/^\s*[-*]\s+(.*)$/);
    if (ul) {
      flushPara();
      if (listType && listType !== "ul") closeList();
      if (!listType) {
        listType = "ul";
        html += "<ul>";
      }
      html += `<li>${inline(ul[1])}</li>`;
      continue;
    }
    if (!line.trim()) {
      flushPara();
      closeList();
      continue;
    }
    para.push(line.trim());
  }
  flushPara();
  closeList();
  if (inCode) html += "</code></pre>";
  el.innerHTML = html;
}

async function drainReasoningNdjsonMarkdownTail(reader, initialTail, mdEl, decoder, opts = {}) {
  let buf = initialTail || "";
  let markdownAcc = mdEl?.dataset.markdownAcc || "";
  const summaryText = mdEl?.dataset.summaryText || "";
  try {
    while (true) {
      const { done, value } = await reader.read();
      if (value) buf += decoder.decode(value, { stream: true });
      for (;;) {
        const n = buf.indexOf("\n");
        if (n < 0) break;
        const line = buf.slice(0, n).trim();
        buf = buf.slice(n + 1);
        if (!line) continue;
        let o;
        try {
          o = JSON.parse(line);
        } catch {
          continue;
        }
        if (o.type === "markdown" && o.text && mdEl) {
          markdownAcc += String(o.text);
          mdEl.dataset.markdownAcc = markdownAcc;
          renderWorkModeMarkdown(mdEl, markdownAcc, summaryText);
          const scrollHost = mdEl.closest(".vera-reasoning-scroll") || mdEl;
          scrollHost.scrollTop = scrollHost.scrollHeight;
        }
      }
      if (done) break;
    }
  } catch (_) {}
  if (typeof opts.onDone === "function") {
    try {
      opts.onDone({ markdownAcc, summaryText });
    } catch (_) {}
  }
}

function extractWorkModeReasoningSummaryAnswerLine(summaryText) {
  const first = String(summaryText || "")
    .replace(/\r/g, "\n")
    .split("\n")
    .map((line) => line.trim())
    .find(Boolean);
  return first || "";
}

function normalizeWorkModeReasoningSummary(summaryText, laneLabel = "") {
  const handoffLine = laneLabel
    ? `Opening full explanation in ${laneLabel}.`
    : "Opening full explanation now.";
  const firstRawLine = String(summaryText || "")
    .replace(/\r/g, "\n")
    .split("\n")
    .map((line) => line.trim())
    .find(Boolean) || "";
  let answerLine = firstRawLine.replace(/\s+/g, " ").trim();
  answerLine = answerLine.replace(/^["']+|["']+$/g, "").trim();
  answerLine = answerLine.replace(/\bI'm opening .*/i, "").trim();
  const sentenceMatch = answerLine.match(/^(.+?[.!?])(?:\s|$)/);
  if (sentenceMatch?.[1]) answerLine = sentenceMatch[1].trim();
  if (!answerLine) answerLine = "Here is the key idea in one line.";
  if (!/[.!?]$/.test(answerLine)) answerLine += ".";
  return {
    answerLine,
    handoffLine,
    text: `${answerLine}\n${handoffLine}`
  };
}

function isLikelyWorkChecklistEditIntent(text) {
  const t = String(text || "").trim().toLowerCase();
  if (!t) return false;
  const hasChecklist = /\bcheck\s*list|checklist\b/.test(t);
  if (hasChecklist && /\b(add|remove)\b/.test(t)) return true;
  if (/\b(update|replace)\b/.test(t) && (/\bwith\b/.test(t) || /\bitem\s+\d+\b/.test(t))) {
    return true;
  }
  return false;
}

async function maybePrepareWorkModeReasoning(formData, trimmed, signal, opts = {}) {
  if (!isVeraWorkModeOn()) return;
  if (isLikelyWorkChecklistEditIntent(trimmed)) return;
  const attachment = opts?.attachment;
  const hasUpload = attachment instanceof File && attachment.size > 0;

  let routeReasoning = false;
  if (hasUpload) {
    routeReasoning = true;
  } else {
    const heuristicReasoning = (() => {
      const t = String(trimmed || "").toLowerCase();
      if (!t) return false;
      const conceptWords = /\b(explain|how does|how do|derive|proof|theorem|compare|trade-?off|framework|architecture|mechanism|intuition)\b/;
      const domainWords = /\b(binomial|black-?scholes|delta|gamma|vega|volatility|probability|equation|calculus|statistics|finance|histor(y|ical)|economics|algorithm)\b/;
      const multiPart = /(\b(step by step|in detail|deep dive|from scratch)\b)|([,:;].+[,:;])/;
      const writingTask =
        /\b(write|draft|compose|polish|rewrite)\b/.test(t) &&
        /\b(email|essay|script|speech|letter|cover letter|proposal|statement|outline)\b/.test(t);
      return (
        (conceptWords.test(t) && domainWords.test(t)) ||
        domainWords.test(t) ||
        multiPart.test(t) ||
        writingTask
      );
    })();

    try {
      const cr = await fetch(`${API_URL}/work_mode/classify`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ session_id: getSessionId(), text: trimmed }),
        signal
      });
      if (cr.ok) {
        const cj = await cr.json();
        routeReasoning = Boolean(cj.prompt_reasoning || cj.reasoning);
      }
    } catch {
      /* fall through to heuristic */
    }
    routeReasoning = routeReasoning || heuristicReasoning;
    if (!routeReasoning) return;
  }

  workModeReasoningConfirmPending = null;
  const laneIdx = await acquireWorkModeReasoningLane();
  const laneLabel = getWorkModeReasoningLaneLabel(laneIdx);
  const laneId = getWorkModeReasoningLaneId(laneIdx);
  const laneAbortController = new AbortController();
  workModeReasoningAbortControllers.set(laneIdx, laneAbortController);
  syncWorkModeReasoningCancelButton();
  const scrollEl = getReasoningScrollElByLane(laneIdx);
  if (!scrollEl) {
    endWorkModeReasoningLaneRun(laneIdx);
    return;
  }
  activateReasoningTab(laneIdx);

  let sr;
  try {
    if (hasUpload) {
      const fd = new FormData();
      fd.append("session_id", getSessionId());
      fd.append("text", trimmed);
      fd.append("lane_id", laneId);
      fd.append("file", attachment);
      sr = await fetch(`${API_URL}/work_mode/reasoning_stream_upload`, {
        method: "POST",
        body: fd,
        signal: laneAbortController.signal
      });
      if (!sr.ok) {
        let msg = `Upload failed (${sr.status})`;
        try {
          const err = await sr.json();
          if (err?.detail) msg = String(err.detail);
        } catch {
          /* ignore */
        }
        setWorkModeAttachmentMeta(msg);
        endWorkModeReasoningLaneRun(laneIdx);
        return "reasoning-upload-failed";
      }
      if (!sr.body) {
        setWorkModeAttachmentMeta("Upload failed: empty response body.");
        endWorkModeReasoningLaneRun(laneIdx);
        return "reasoning-upload-failed";
      }
    } else {
      sr = await fetch(`${API_URL}/work_mode/reasoning_stream`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ session_id: getSessionId(), text: trimmed, lane_id: laneId }),
        signal: laneAbortController.signal
      });
      if (!sr.ok || !sr.body) {
        endWorkModeReasoningLaneRun(laneIdx);
        return;
      }
    }
  } catch (err) {
    endWorkModeReasoningLaneRun(laneIdx);
    throw err;
  }

  const turnEl = appendReasoningTurnMount(scrollEl);
  if (!turnEl) {
    endWorkModeReasoningLaneRun(laneIdx);
    return;
  }
  turnEl.dataset.markdownAcc = "";
  turnEl.dataset.summaryText = "";
  const reader = sr.body.getReader();
  const decoder = new TextDecoder();
  let lineBuf = "";
  let foundSummary = false;
  try {
    while (!foundSummary) {
      const { done, value } = await reader.read();
      if (done && !value) break;
      if (value) lineBuf += decoder.decode(value, { stream: true });
      for (;;) {
        const n = lineBuf.indexOf("\n");
        if (n < 0) break;
        const line = lineBuf.slice(0, n).trim();
        lineBuf = lineBuf.slice(n + 1);
        if (!line) continue;
        let o;
        try {
          o = JSON.parse(line);
        } catch {
          continue;
        }
        if (o.type === "error") break;
        if (o.type === "summary" && o.text) {
          const normalizedSummary = normalizeWorkModeReasoningSummary(String(o.text), laneLabel);
          turnEl.dataset.summaryText = normalizedSummary.text;
          formData.append("reasoning_voice_coach", normalizedSummary.text);
          foundSummary = true;
          break;
        }
      }
    }
  } catch (_) {}
  if (foundSummary) {
    void drainReasoningNdjsonMarkdownTail(reader, lineBuf, turnEl, decoder, {
      onDone: ({ markdownAcc, summaryText }) => {
        setReasoningTabTopicFromFinal(turnEl, {
          summaryText: extractWorkModeReasoningSummaryAnswerLine(summaryText),
          markdownText: markdownAcc,
          userPrompt: trimmed
        });
        endWorkModeReasoningLaneRun(laneIdx);
      }
    });
  } else {
    endWorkModeReasoningLaneRun(laneIdx);
  }
  scrollEl.scrollTop = scrollEl.scrollHeight;
}

function setWorkModeAttachmentMeta(message) {
  const meta = document.getElementById("vera-reasoning-attach-meta");
  if (!meta) return;
  meta.textContent = message || "";
}

/** Text-only reasoning stream into the reasoning panel (no `/infer`). File uploads use `maybePrepareWorkModeReasoning` + typed infer instead. */
async function streamWorkModeReasoningComposer(text, signal) {
  const laneIdx = await acquireWorkModeReasoningLane();
  const laneLabel = getWorkModeReasoningLaneLabel(laneIdx);
  const laneId = getWorkModeReasoningLaneId(laneIdx);
  const laneAbortController = new AbortController();
  workModeReasoningAbortControllers.set(laneIdx, laneAbortController);
  syncWorkModeReasoningCancelButton();
  const scrollEl = getReasoningScrollElByLane(laneIdx);
  if (!scrollEl) {
    endWorkModeReasoningLaneRun(laneIdx);
    return;
  }
  activateReasoningTab(laneIdx);
  let summaryText = "";
  let markdownAcc = "";
  try {
    const sr = await fetch(`${API_URL}/work_mode/reasoning_stream`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ session_id: getSessionId(), text, lane_id: laneId }),
      signal: laneAbortController.signal
    });
    if (!sr.ok) {
      let msg = `Reasoning failed (${sr.status})`;
      try {
        const err = await sr.json();
        if (err?.detail) msg = String(err.detail);
      } catch {
        /* ignore */
      }
      setWorkModeAttachmentMeta(msg);
      return;
    }
    if (!sr.body) {
      setWorkModeAttachmentMeta("Reasoning failed: empty response body.");
      return;
    }

    const turnEl = appendReasoningTurnMount(scrollEl);
    if (!turnEl) return;
    turnEl.dataset.markdownAcc = "";
    turnEl.dataset.summaryText = "";

    const reader = sr.body.getReader();
    const decoder = new TextDecoder();
    let buf = "";
    try {
      while (true) {
        const { done, value } = await reader.read();
        if (value) buf += decoder.decode(value, { stream: true });
        for (;;) {
          const n = buf.indexOf("\n");
          if (n < 0) break;
          const line = buf.slice(0, n).trim();
          buf = buf.slice(n + 1);
          if (!line) continue;
          let o;
          try {
            o = JSON.parse(line);
          } catch {
            continue;
          }
          if (o.type === "summary" && o.text) {
            summaryText = normalizeWorkModeReasoningSummary(String(o.text), laneLabel).text;
            turnEl.dataset.summaryText = summaryText;
            renderWorkModeMarkdown(turnEl, markdownAcc, summaryText);
          }
          if (o.type === "markdown" && o.text) {
            markdownAcc += String(o.text);
            turnEl.dataset.markdownAcc = markdownAcc;
            renderWorkModeMarkdown(turnEl, markdownAcc, summaryText);
          }
        }
        if (done) break;
      }
    } catch (_) {}
    setReasoningTabTopicFromFinal(turnEl, {
      summaryText: extractWorkModeReasoningSummaryAnswerLine(summaryText),
      markdownText: markdownAcc,
      userPrompt: text
    });
    scrollEl.scrollTop = scrollEl.scrollHeight;
  } finally {
    endWorkModeReasoningLaneRun(laneIdx);
  }
}

function createWorkChecklistDragHandle() {
  const handle = document.createElement("div");
  handle.className = "vera-wm-checklist-drag-handle";
  handle.setAttribute("aria-label", "Drag to reorder");
  const dots = document.createElement("div");
  dots.className = "vera-wm-checklist-drag-dots";
  dots.setAttribute("aria-hidden", "true");
  for (let i = 0; i < 6; i += 1) dots.appendChild(document.createElement("span"));
  handle.appendChild(dots);
  return handle;
}

const WORK_CHECKLIST_SUBITEM_INDENT_THRESHOLD_PX = 26;
let workChecklistDragSession = { id: "", startX: 0, lastX: 0 };

function readChecklistItemsFromStorageSafe() {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    const parsed = raw ? JSON.parse(raw) : [];
    return Array.isArray(parsed) ? parsed : [];
  } catch {
    return [];
  }
}

function writeChecklistItemsToStorageSafe(items) {
  try {
    markWorkChecklistLocalMutation();
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(items));
    queueWorkChecklistSyncToServer();
    return true;
  } catch {
    return false;
  }
}

function isChecklistDescendant(items, maybeChildId, maybeAncestorId) {
  const map = new Map(items.map((x) => [String(x?.id || ""), String(x?.parent_id || "")]));
  let cur = String(maybeChildId || "");
  const ancestor = String(maybeAncestorId || "");
  if (!cur || !ancestor) return false;
  let guard = 0;
  while (guard < 200) {
    const p = map.get(cur);
    if (!p) return false;
    if (p === ancestor) return true;
    cur = p;
    guard += 1;
  }
  return false;
}

function applyChecklistNestingFromDrag(draggedId) {
  const sid = String(draggedId || "");
  if (!sid) return false;
  const dx = Number(workChecklistDragSession.lastX) - Number(workChecklistDragSession.startX);
  if (!Number.isFinite(dx) || Math.abs(dx) < WORK_CHECKLIST_SUBITEM_INDENT_THRESHOLD_PX) return false;
  const items = readChecklistItemsFromStorageSafe();
  const idx = items.findIndex((x) => String(x?.id || "") === sid);
  if (idx < 0) return false;
  const dragged = items[idx];
  if (!dragged || typeof dragged.text !== "string") return false;

  if (dx <= -WORK_CHECKLIST_SUBITEM_INDENT_THRESHOLD_PX) {
    if (!dragged.parent_id) return false;
    items[idx] = { ...dragged, parent_id: null };
    return writeChecklistItemsToStorageSafe(items);
  }

  let parentCandidate = null;
  for (let i = idx - 1; i >= 0; i -= 1) {
    const prev = items[i];
    if (!prev || String(prev.id || "") === sid) continue;
    if (Boolean(prev.done) !== Boolean(dragged.done)) continue;
    if (prev.parent_id) continue;
    parentCandidate = prev;
    break;
  }
  if (!parentCandidate?.id) return false;
  const pid = String(parentCandidate.id);
  if (pid === sid) return false;
  if (isChecklistDescendant(items, pid, sid)) return false;
  items[idx] = { ...dragged, parent_id: pid };
  return writeChecklistItemsToStorageSafe(items);
}

function workChecklistInsertBeforeFromY(container, clientY) {
  const dragging = container.querySelector(":scope > li.vera-wm-checklist-dragging");
  const lis = [...container.querySelectorAll(":scope > li")].filter((el) => el !== dragging);
  for (const child of lis) {
    const r = child.getBoundingClientRect();
    if (clientY < r.top + r.height / 2) return child;
  }
  return null;
}

function persistWorkChecklistOrderFromDom() {
  const ongoingUl = document.getElementById("vera-wm-checklist-ongoing");
  const completedUl = document.getElementById("vera-wm-checklist-completed");
  if (!ongoingUl || !completedUl) return;
  const ongoingIds = [...ongoingUl.querySelectorAll(":scope > li")].map((el) => el.dataset.id).filter(Boolean);
  const completedIds = [...completedUl.querySelectorAll(":scope > li")].map((el) => el.dataset.id).filter(Boolean);
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items)) items = [];
    const map = new Map(items.map((x) => [String(x.id), x]));
    const next = [...ongoingIds, ...completedIds].map((id) => map.get(id)).filter(Boolean);
    if (next.length !== items.length) return;
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(next));
    queueWorkChecklistSyncToServer();
  } catch (_) {}
}

function applyWorkChecklistCompletedCollapseFromStorage() {
  const pane = document.getElementById("vera-wm-checklist-pane");
  const btn = document.getElementById("vera-wm-checklist-completed-toggle");
  if (!pane || !btn || pane.classList.contains("vera-wm-checklist-pane--ongoing-only")) return;
  let collapsed = false;
  try {
    collapsed = localStorage.getItem(WORK_CHECKLIST_COMPLETED_COLLAPSED_KEY) === "1";
  } catch (_) {}
  pane.classList.toggle("vera-wm-checklist-pane--completed-collapsed", collapsed);
  btn.setAttribute("aria-expanded", collapsed ? "false" : "true");
}

function wireWorkChecklistCompletedCollapse() {
  const btn = document.getElementById("vera-wm-checklist-completed-toggle");
  const pane = document.getElementById("vera-wm-checklist-pane");
  if (!btn || !pane || btn.dataset.collapseWired === "1") return;
  btn.dataset.collapseWired = "1";
  btn.addEventListener("click", () => {
    if (pane.classList.contains("vera-wm-checklist-pane--ongoing-only")) return;
    const collapsed = !pane.classList.contains("vera-wm-checklist-pane--completed-collapsed");
    pane.classList.toggle("vera-wm-checklist-pane--completed-collapsed", collapsed);
    btn.setAttribute("aria-expanded", collapsed ? "false" : "true");
    try {
      localStorage.setItem(WORK_CHECKLIST_COMPLETED_COLLAPSED_KEY, collapsed ? "1" : "0");
      queueWorkChecklistSyncToServer();
    } catch (_) {}
  });
}

function ensureWorkChecklistListDnD() {
  const ongoingUl = document.getElementById("vera-wm-checklist-ongoing");
  const completedUl = document.getElementById("vera-wm-checklist-completed");
  if (!ongoingUl || !completedUl || ongoingUl.dataset.checklistDnd === "1") return;
  ongoingUl.dataset.checklistDnd = "1";
  completedUl.dataset.checklistDnd = "1";

  const onDragOver = (e) => {
    const ul = e.currentTarget;
    if (!(ul instanceof HTMLElement)) return;
    e.preventDefault();
    workChecklistDragSession.lastX = Number(e.clientX) || workChecklistDragSession.lastX;
    try {
      e.dataTransfer.dropEffect = "move";
    } catch (_) {}
    const dragging = ul.querySelector(":scope > li.vera-wm-checklist-dragging");
    if (!dragging) return;
    const insertBefore = workChecklistInsertBeforeFromY(ul, e.clientY);
    if (insertBefore === null) ul.appendChild(dragging);
    else ul.insertBefore(dragging, insertBefore);
  };

  ongoingUl.addEventListener("dragover", onDragOver);
  completedUl.addEventListener("dragover", onDragOver);
}

/**
 * If the first row is an empty ongoing placeholder but completed items follow it in storage,
 * the placeholder was likely inserted at index 0 (legacy bug). Rotate it to the end so it
 * stays the trailing “new item” slot, not a stray row above completed tasks.
 */
function normalizeWorkChecklistLeadingPlaceholderInStorage() {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items) || items.length < 2) return false;
    const first = items[0];
    if (!first || typeof first.text !== "string" || Boolean(first.done)) return false;
    if (String(first.text).trim() !== "") return false;
    if (!items.slice(1).some((x) => x && Boolean(x.done))) return false;
    const [head, ...rest] = items;
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify([...rest, head]));
    queueWorkChecklistSyncToServer();
    return true;
  } catch (_) {
    return false;
  }
}

/** Drops empty ongoing rows except the bottom-most one (storage order among !done items). */
function pruneInteriorEmptyOngoingItems() {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items)) items = [];
    const valid = (x) => x && typeof x.text === "string";
    const ongoingIndices = [];
    for (let i = 0; i < items.length; i += 1) {
      if (valid(items[i]) && !Boolean(items[i].done)) ongoingIndices.push(i);
    }
    if (ongoingIndices.length <= 1) return false;
    const toRemove = [];
    for (let j = 0; j < ongoingIndices.length - 1; j += 1) {
      const i = ongoingIndices[j];
      if (String(items[i].text).trim() === "") toRemove.push(i);
    }
    if (toRemove.length === 0) return false;
    toRemove.sort((a, b) => b - a);
    for (const i of toRemove) items.splice(i, 1);
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(items));
    queueWorkChecklistSyncToServer();
    return true;
  } catch (_) {
    return false;
  }
}

/** Ensures the last ongoing row is always an empty slot for new text (no separate “+” row). */
function ensureWorkChecklistTrailingEmptyOngoing() {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items)) items = [];
    const valid = (x) => x && typeof x.text === "string";
    let lastOngoingIndex = -1;
    for (let i = 0; i < items.length; i += 1) {
      if (valid(items[i]) && !Boolean(items[i].done)) lastOngoingIndex = i;
    }
    const lastOngoing = lastOngoingIndex >= 0 ? items[lastOngoingIndex] : null;
    const needNew =
      lastOngoingIndex < 0 || !lastOngoing || String(lastOngoing.text).trim() !== "";
    if (!needNew) return false;
    const id = `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
    /* When there are no ongoing rows yet, append at list end — never splice(0,0) or the empty slot sits above completed items in storage order. */
    if (lastOngoingIndex < 0) {
      items.push({ id, text: "", done: false, parent_id: null });
    } else {
      items.splice(lastOngoingIndex + 1, 0, { id, text: "", done: false, parent_id: null });
    }
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(items));
    queueWorkChecklistSyncToServer();
    return true;
  } catch (_) {
    return false;
  }
}

/** Insert a new empty ongoing row immediately after the given ongoing item (by storage order). */
function insertWorkChecklistEmptyOngoingAfter(afterId) {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items)) items = [];
    const idx = items.findIndex((x) => x && String(x.id) === String(afterId));
    if (idx < 0) return null;
    const row = items[idx];
    if (!row || typeof row.text !== "string" || Boolean(row.done)) return null;
    const nid = `${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
    items.splice(idx + 1, 0, { id: nid, text: "", done: false, parent_id: null });
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(items));
    queueWorkChecklistSyncToServer();
    return nid;
  } catch (_) {
    return null;
  }
}

function loadWorkChecklistItems() {
  const ongoingUl = document.getElementById("vera-wm-checklist-ongoing");
  const completedUl = document.getElementById("vera-wm-checklist-completed");
  if (!ongoingUl || !completedUl) return;
  ensureWorkChecklistListDnD();
  normalizeWorkChecklistLeadingPlaceholderInStorage();
  /* Do not call pruneInteriorEmptyOngoingItems on load — it would remove intentional mid-list empties from Enter. */
  let guard = 0;
  while (ensureWorkChecklistTrailingEmptyOngoing()) {
    guard += 1;
    if (guard > 10) break;
  }
  let items = [];
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    if (raw) items = JSON.parse(raw);
    if (!Array.isArray(items)) items = [];
  } catch {
    items = [];
  }
  const idMap = new Map(items.map((x) => [String(x?.id || ""), x]));
  const depthCache = new Map();
  const getDepth = (id) => {
    const sid = String(id || "");
    if (!sid) return 0;
    if (depthCache.has(sid)) return depthCache.get(sid);
    let depth = 0;
    let cur = idMap.get(sid);
    const visited = new Set([sid]);
    while (cur && cur.parent_id && depth < 1) {
      const pid = String(cur.parent_id || "");
      if (!pid || visited.has(pid)) break;
      const parent = idMap.get(pid);
      if (!parent || Boolean(parent.done) !== Boolean(cur.done)) break;
      visited.add(pid);
      depth += 1;
      cur = parent;
    }
    depthCache.set(sid, depth);
    return depth;
  };
  ongoingUl.replaceChildren();
  completedUl.replaceChildren();
  items.forEach((it) => {
    if (!it || typeof it.text !== "string") return;
    const id = String(it.id || "");
    const li = document.createElement("li");
    li.className = "vera-wm-checklist-li";
    if (it.done) li.classList.add("is-done");
    li.dataset.id = id;
    li.style.setProperty("--checklist-depth", String(getDepth(id)));
    li.draggable = false;

    const handle = createWorkChecklistDragHandle();
    handle.draggable = true;
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.className = "vera-wm-checklist-cb";
    cb.checked = Boolean(it.done);
    cb.setAttribute("aria-label", it.done ? "Mark as not done" : "Mark complete");
    const actions = document.createElement("div");
    actions.className = "vera-wm-checklist-li-actions";

    const btnDel = document.createElement("button");
    btnDel.type = "button";
    btnDel.className = "vera-wm-checklist-action vera-wm-checklist-action-del";
    btnDel.textContent = "✕";
    btnDel.setAttribute("aria-label", "Delete item");
    btnDel.title = "Delete";

    actions.appendChild(btnDel);

    /* dragstart targets the draggable node; with draggable on <li>, e.target was often
       the <li> itself, so closest(handle) failed and every drag was cancelled. */
    handle.addEventListener("dragstart", (e) => {
      e.stopPropagation();
      li.classList.add("vera-wm-checklist-dragging");
      workChecklistDragSession = {
        id,
        startX: Number(e.clientX) || 0,
        lastX: Number(e.clientX) || 0,
      };
      e.dataTransfer.effectAllowed = "move";
      try {
        e.dataTransfer.setData("text/plain", id);
      } catch (_) {}
      try {
        const r = li.getBoundingClientRect();
        e.dataTransfer.setDragImage(li, Math.round(e.clientX - r.left), Math.round(e.clientY - r.top));
      } catch (_) {}
    });
    handle.addEventListener("dragend", () => {
      li.classList.remove("vera-wm-checklist-dragging");
      persistWorkChecklistOrderFromDom();
      applyChecklistNestingFromDrag(id);
      workChecklistDragSession = { id: "", startX: 0, lastX: 0 };
      const pruned = pruneInteriorEmptyOngoingItems();
      const ensured = ensureWorkChecklistTrailingEmptyOngoing();
      if (pruned || ensured) loadWorkChecklistItems();
      else loadWorkChecklistItems();
    });

    btnDel.addEventListener("click", () => {
      persistWorkChecklistRemove(id);
      loadWorkChecklistItems();
    });

    cb.addEventListener("change", () => {
      const wantDone = cb.checked;
      const reduceMotion =
        typeof window.matchMedia === "function" &&
        window.matchMedia("(prefers-reduced-motion: reduce)").matches;

      if (wantDone && !it.done) {
        const textInp = li.querySelector(".vera-wm-checklist-task-input");
        const t = textInp instanceof HTMLInputElement ? textInp.value : it.text;
        if (!String(t ?? "").trim()) {
          cb.checked = false;
          return;
        }
        if (textInp instanceof HTMLInputElement) persistWorkChecklistUpdateText(id, textInp.value);

        if (reduceMotion) {
          persistWorkChecklistToggle(id, true);
          loadWorkChecklistItems();
          return;
        }

        li.classList.add("vera-wm-checklist-li-exiting");
        let finished = false;
        const complete = () => {
          if (finished) return;
          finished = true;
          window.clearTimeout(fallbackTimer);
          li.removeEventListener("transitionend", onTransitionEnd);
          persistWorkChecklistToggle(id, true);
          loadWorkChecklistItems();
          queueWorkChecklistRowEnterAnimation("vera-wm-checklist-completed", id);
        };
        const onTransitionEnd = (ev) => {
          if (ev.target !== li) return;
          if (ev.propertyName !== "opacity" && ev.propertyName !== "filter") return;
          complete();
        };
        const fallbackTimer = window.setTimeout(complete, 420);
        li.addEventListener("transitionend", onTransitionEnd);
        return;
      }

      if (!wantDone && it.done) {
        if (reduceMotion) {
          persistWorkChecklistToggle(id, false);
          loadWorkChecklistItems();
          return;
        }

        li.classList.add("vera-wm-checklist-li-exiting");
        let finished = false;
        const complete = () => {
          if (finished) return;
          finished = true;
          window.clearTimeout(fallbackTimer);
          li.removeEventListener("transitionend", onTransitionEnd);
          persistWorkChecklistToggle(id, false);
          loadWorkChecklistItems();
          queueWorkChecklistRowEnterAnimation("vera-wm-checklist-ongoing", id);
        };
        const onTransitionEnd = (ev) => {
          if (ev.target !== li) return;
          if (ev.propertyName !== "opacity" && ev.propertyName !== "filter") return;
          complete();
        };
        const fallbackTimer = window.setTimeout(complete, 420);
        li.addEventListener("transitionend", onTransitionEnd);
        return;
      }

      persistWorkChecklistToggle(id, wantDone);
      loadWorkChecklistItems();
    });

    if (it.done) {
      const span = document.createElement("span");
      span.className = "vera-wm-checklist-task-text";
      span.textContent = it.text;
      li.appendChild(handle);
      li.appendChild(cb);
      li.appendChild(span);
      li.appendChild(actions);
    } else {
      const inp = document.createElement("input");
      inp.type = "text";
      inp.className = "vera-wm-checklist-task-input";
      inp.placeholder = "List item";
      inp.value = it.text;
      inp.maxLength = 200;
      inp.autocomplete = "off";
      inp.draggable = false;
      inp.addEventListener("keydown", (e) => {
        if (e.key === "ArrowUp" || e.key === "ArrowDown") {
          const ongoingUl = document.getElementById("vera-wm-checklist-ongoing");
          if (!ongoingUl) return;
          const inputs = [...ongoingUl.querySelectorAll(".vera-wm-checklist-task-input")];
          const rowIdx = inputs.indexOf(inp);
          if (rowIdx < 0) return;
          const len = inp.value.length;
          const sel0 = inp.selectionStart ?? 0;
          const sel1 = inp.selectionEnd ?? 0;
          if (e.key === "ArrowDown") {
            if (sel0 !== len || sel1 !== len) return;
            const next = inputs[rowIdx + 1];
            if (next instanceof HTMLInputElement) {
              e.preventDefault();
              next.focus();
              next.setSelectionRange(0, 0);
            }
            return;
          }
          if (sel0 !== 0 || sel1 !== 0) return;
          const prev = inputs[rowIdx - 1];
          if (prev instanceof HTMLInputElement) {
            e.preventDefault();
            prev.focus();
            const pl = prev.value.length;
            prev.setSelectionRange(pl, pl);
          }
          return;
        }
        if (e.key !== "Enter" || e.shiftKey) return;
        e.preventDefault();
        persistWorkChecklistUpdateText(id, inp.value);
        const newId = insertWorkChecklistEmptyOngoingAfter(id);
        loadWorkChecklistItems();
        window.requestAnimationFrame(() => {
          window.requestAnimationFrame(() => {
            const ul = document.getElementById("vera-wm-checklist-ongoing");
            const sel = newId
              ? `li[data-id="${newId}"] .vera-wm-checklist-task-input`
              : "li:last-child .vera-wm-checklist-task-input";
            const nextInp = ul?.querySelector(sel);
            if (nextInp instanceof HTMLInputElement) nextInp.focus();
          });
        });
      });
      inp.addEventListener("blur", () => {
        window.setTimeout(() => {
          const next = document.activeElement;
          if (next && li.contains(next)) {
            persistWorkChecklistUpdateText(id, inp.value);
            return;
          }
          persistWorkChecklistUpdateText(id, inp.value);
          /* replaceChildren (e.g. after Enter) detaches this row; blur still fires — do not treat as “abandon middle empty”. */
          if (!li.isConnected) return;
          const ul = document.getElementById("vera-wm-checklist-ongoing");
          const siblings = ul ? [...ul.querySelectorAll(":scope > li")] : [];
          const rowIdx = siblings.indexOf(li);
          if (rowIdx < 0) return;
          const isLastOngoing = rowIdx === siblings.length - 1;
          let removedMiddle = false;
          if (!inp.value.trim() && !isLastOngoing) {
            persistWorkChecklistRemove(id);
            removedMiddle = true;
          }
          /* Do not prune all interior empties on every blur — that removed a new Enter row when focus moved to another item. */
          const ensured = ensureWorkChecklistTrailingEmptyOngoing();
          if (removedMiddle || ensured) loadWorkChecklistItems();
        }, 0);
      });
      li.appendChild(handle);
      li.appendChild(cb);
      li.appendChild(inp);
      li.appendChild(actions);
    }
    (it.done ? completedUl : ongoingUl).appendChild(li);
  });

  const pane = document.getElementById("vera-wm-checklist-pane");
  const completedSection = document.getElementById("vera-wm-checklist-completed-section");
  /* Use rows actually rendered — items with done:true but invalid text are skipped in forEach
     but used to be counted here, which left an empty “Completed” chrome visible. */
  const completedCount = completedUl.querySelectorAll(":scope > li").length;
  const countEl = document.getElementById("vera-wm-checklist-completed-count");
  if (countEl) countEl.textContent = completedCount ? ` (${completedCount})` : "";
  if (completedSection && pane) {
    if (completedCount === 0) {
      completedSection.hidden = true;
      completedSection.classList.add("vera-wm-checklist-completed-section--empty");
      pane.classList.add("vera-wm-checklist-pane--ongoing-only");
      pane.classList.remove("vera-wm-checklist-pane--completed-collapsed");
    } else {
      completedSection.hidden = false;
      completedSection.classList.remove("vera-wm-checklist-completed-section--empty");
      pane.classList.remove("vera-wm-checklist-pane--ongoing-only");
      applyWorkChecklistCompletedCollapseFromStorage();
    }
  }
  syncWorkChecklistHelpPlanButton();
}

function persistWorkChecklistToggle(id, done) {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items)) items = [];
    items = items.map((x) =>
      String(x.id) === id ? { ...x, done: Boolean(done) } : x
    );
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(items));
    queueWorkChecklistSyncToServer();
  } catch (_) {}
}

function persistWorkChecklistUpdateText(id, text) {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items)) items = [];
    items = items.map((x) => (String(x.id) === id ? { ...x, text: String(text) } : x));
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(items));
    queueWorkChecklistSyncToServer();
  } catch (_) {}
}

function persistWorkChecklistRemove(id) {
  try {
    const raw = localStorage.getItem(WORK_CHECKLIST_STORAGE_KEY);
    let items = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(items)) items = [];
    items = items.filter((x) => String(x.id) !== id);
    localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(items));
    queueWorkChecklistSyncToServer();
  } catch (_) {}
}

const WORK_CHECKLIST_HELP_PLAN_MAX_ITEMS = 24;

function collectWorkChecklistOngoingTexts() {
  const ul = document.getElementById("vera-wm-checklist-ongoing");
  if (!ul) return [];
  const out = [];
  for (const li of ul.querySelectorAll(":scope > li")) {
    const inp = li.querySelector(".vera-wm-checklist-task-input");
    if (inp instanceof HTMLInputElement) {
      const t = inp.value.trim();
      if (t) out.push(t);
    }
  }
  return out;
}

function syncWorkChecklistHelpPlanButton() {
  const btn = document.getElementById("vera-wm-checklist-help-plan");
  if (!btn) return;
  btn.disabled = collectWorkChecklistOngoingTexts().length === 0;
}

let workChecklistPlanHintTimer = null;
function flashWorkChecklistPlanHint(message) {
  const el = document.getElementById("vera-wm-checklist-plan-hint");
  if (!el) return;
  if (workChecklistPlanHintTimer) {
    window.clearTimeout(workChecklistPlanHintTimer);
    workChecklistPlanHintTimer = null;
  }
  el.textContent = message;
  workChecklistPlanHintTimer = window.setTimeout(() => {
    el.textContent = "";
    workChecklistPlanHintTimer = null;
  }, 4500);
}

function buildWorkChecklistHelpPlanUserMessage(lines) {
  const cap = lines.slice(0, WORK_CHECKLIST_HELP_PLAN_MAX_ITEMS);
  const body = cap.map((t, i) => `${i + 1}. ${t}`).join("\n");
  const more =
    lines.length > WORK_CHECKLIST_HELP_PLAN_MAX_ITEMS
      ? `\n… (${lines.length - WORK_CHECKLIST_HELP_PLAN_MAX_ITEMS} more items not shown)\n`
      : "";
  return (
    "[Planning help — keep the reply concise. Use short bullets: sensible order or prep, easy-to-miss details (fuel, timing, gear, transitions). End with a short numbered list of specific questions to narrow things down (goals, time windows, cuisine, muscle focus, equipment, budget, constraints).]\n\n" +
    "Ongoing checklist (in order):\n" +
    body +
    more
  );
}

let workChecklistPlanRequestInFlight = false;

function isWorkChecklistPlanShortcutIntent(text) {
  const t = String(text || "").toLowerCase().trim();
  if (!t) return false;
  const hasPlanVerb = /\b(plan|planning|roadmap|prioriti[sz]e|break\s*(it\s*)?down|organi[sz]e)\b/.test(t);
  const hasChecklistNoun = /\b(check\s*list|checklist|to-?do|todo|task list|tasks?)\b/.test(t);
  const directPhrase = /\b(help me plan|can you help me plan)\b/.test(t);
  return (hasPlanVerb && hasChecklistNoun) || (directPhrase && hasChecklistNoun);
}

async function runWorkChecklistHelpPlan({ signal } = {}) {
  if (!isVeraWorkModeOn()) return false;
  if (workChecklistPlanRequestInFlight) return true;
  const lines = collectWorkChecklistOngoingTexts();
  if (!lines.length) {
    flashWorkChecklistPlanHint("Add text to at least one ongoing item first.");
    return true;
  }
  const text = buildWorkChecklistHelpPlanUserMessage(lines);
  const helpPlanBtn = document.getElementById("vera-wm-checklist-help-plan");
  workChecklistPlanRequestInFlight = true;
  if (helpPlanBtn instanceof HTMLButtonElement) helpPlanBtn.disabled = true;
  try {
    const reasoningScroll = getActiveReasoningScrollEl();
    if (reasoningScroll instanceof HTMLElement) {
      reasoningScroll.scrollIntoView({ behavior: "smooth", block: "nearest" });
    }
    await streamWorkModeReasoningComposer(text, signal);
  } finally {
    workChecklistPlanRequestInFlight = false;
    syncWorkChecklistHelpPlanButton();
  }
  return true;
}

async function maybeHandleWorkChecklistPlanShortcut(text, signal) {
  if (!isVeraWorkModeOn() || appModePrefix() !== "vera") return false;
  if (!isWorkChecklistPlanShortcutIntent(text)) return false;
  await runWorkChecklistHelpPlan({ signal });
  return true;
}

function queueWorkChecklistRowEnterAnimation(ulId, taskId) {
  const sid = String(taskId || "");
  if (!sid || !ulId) return;
  const run = () => {
    const ul = document.getElementById(ulId);
    if (!ul) return;
    const esc =
      typeof CSS !== "undefined" && typeof CSS.escape === "function"
        ? CSS.escape(sid)
        : sid.replace(/["\\]/g, "");
    const moved = ul.querySelector(`:scope > li[data-id="${esc}"]`);
    if (!(moved instanceof HTMLElement)) return;
    moved.classList.add("vera-wm-checklist-li-entering");
    const done = () => {
      moved.removeEventListener("animationend", done);
      moved.classList.remove("vera-wm-checklist-li-entering");
    };
    moved.addEventListener("animationend", done, { once: true });
  };
  window.requestAnimationFrame(() => window.requestAnimationFrame(run));
}

function wireWorkModeChecklistAndComposer() {
  ensureWorkChecklistListDnD();
  wireWorkChecklistCompletedCollapse();
  wireWorkModeLeftPaneLayout();
  applyWorkModeLeftPaneLayoutFromStorage();
  const rs = document.getElementById("vera-reasoning-send");
  const cancelBtn = document.getElementById("vera-reasoning-cancel");
  const ri = document.getElementById("vera-reasoning-input");
  const attachBtn = document.getElementById("vera-reasoning-attach-btn");
  const fileInput = document.getElementById("vera-reasoning-file");
  const applyReasoningAttachmentFile = (f) => {
    if (!f) {
      workModeReasoningAttachment = null;
      if (fileInput) fileInput.value = "";
      setWorkModeAttachmentMeta("");
      return false;
    }
    const name = (f.name || "").toLowerCase();
    const isPdf = name.endsWith(".pdf") || (f.type || "").includes("pdf");
    const isImage = (f.type || "").startsWith("image/") || /\.(png|jpe?g|webp)$/.test(name);
    if (!isPdf && !isImage) {
      workModeReasoningAttachment = null;
      if (fileInput) fileInput.value = "";
      setWorkModeAttachmentMeta("Unsupported file. Use one PDF or image.");
      return false;
    }
    if (f.size > 25 * 1024 * 1024) {
      workModeReasoningAttachment = null;
      if (fileInput) fileInput.value = "";
      setWorkModeAttachmentMeta("File too large. Max 25MB.");
      return false;
    }
    workModeReasoningAttachment = f;
    setWorkModeAttachmentMeta(`Attached: ${f.name}`);
    return true;
  };
  attachBtn?.addEventListener("click", () => fileInput?.click());
  fileInput?.addEventListener("change", () => {
    const f = fileInput.files?.[0] || null;
    applyReasoningAttachmentFile(f);
  });

  const submitWorkModeReasoningComposer = async () => {
    const t = ri?.value.trim() ?? "";
    if (!t) return;
    if (!isVeraWorkModeOn()) return;
    if (ri) ri.value = "";
    if (workModeReasoningAttachment) {
      const att = workModeReasoningAttachment;
      try {
        await sendVeraWorkModeTypedInferTurn(t, {
          path: "reasoning-composer-upload",
          reasoningAttachment: att
        });
      } catch (err) {
        console.warn("[WorkMode] reasoning composer upload", err);
      } finally {
        workModeReasoningAttachment = null;
        if (fileInput) fileInput.value = "";
        setWorkModeAttachmentMeta("");
      }
      return;
    }
    try {
      await sendVeraWorkModeTypedInferTurn(t, { path: "reasoning-composer" });
    } catch (err) {
      console.warn("[WorkMode] reasoning composer", err);
    }
  };

  rs?.addEventListener("click", () => {
    void submitWorkModeReasoningComposer();
  });
  cancelBtn?.addEventListener("click", () => {
    const activeIdx = getActiveReasoningLaneIndex();
    if (activeIdx == null) return;
    cancelWorkModeReasoningLane(activeIdx);
  });
  syncWorkModeReasoningCancelButton();
  ri?.addEventListener("keydown", (e) => {
    if (e.key !== "Enter" || e.shiftKey) return;
    e.preventDefault();
    void submitWorkModeReasoningComposer();
  });
  ri?.addEventListener("paste", (e) => {
    const cd = e.clipboardData;
    if (!cd?.items?.length) return;
    let imageFile = null;
    for (const item of cd.items) {
      if (!item || item.kind !== "file") continue;
      if ((item.type || "").startsWith("image/")) {
        imageFile = item.getAsFile();
        if (imageFile) break;
      }
    }
    if (!imageFile) return;
    const ext = (imageFile.type || "").includes("png")
      ? "png"
      : (imageFile.type || "").includes("webp")
      ? "webp"
      : "jpg";
    const stamped = new File([imageFile], `pasted-image-${Date.now()}.${ext}`, {
      type: imageFile.type || "image/png",
    });
    const ok = applyReasoningAttachmentFile(stamped);
    if (ok) e.preventDefault();
  });

  const ongoingUlPlan = document.getElementById("vera-wm-checklist-ongoing");
  if (ongoingUlPlan && ongoingUlPlan.dataset.helpPlanInput !== "1") {
    ongoingUlPlan.dataset.helpPlanInput = "1";
    ongoingUlPlan.addEventListener("input", () => {
      syncWorkChecklistHelpPlanButton();
    });
  }

  const helpPlanBtn = document.getElementById("vera-wm-checklist-help-plan");
  if (helpPlanBtn && helpPlanBtn.dataset.wiredHelpPlan !== "1") {
    helpPlanBtn.dataset.wiredHelpPlan = "1";
    helpPlanBtn.addEventListener("click", async () => {
      try {
        await runWorkChecklistHelpPlan();
      } catch (err) {
        console.warn("[WorkMode] help me plan", err);
      }
    });
  }
  syncWorkChecklistHelpPlanButton();
}

wireWorkModeChecklistAndComposer();
loadWorkChecklistItems();
window.loadWorkModeChecklist = loadWorkChecklistItems;
window.hydrateWorkModeChecklistFromServer = hydrateWorkChecklistFromServer;
migrateLegacyVeraChatStorageKey();
restoreVeraChatState();
wireReasoningTabStrip();

let veraHeaderDateTimeTimer = null;

function stopVeraHeaderDateTime() {
  if (veraHeaderDateTimeTimer) {
    clearInterval(veraHeaderDateTimeTimer);
    veraHeaderDateTimeTimer = null;
  }
}

function wireVeraHeaderDateTime() {
  const timeEl = document.getElementById("vera-datetime-time");
  const dateEl = document.getElementById("vera-datetime-date");
  if (!timeEl || !dateEl) return;
  stopVeraHeaderDateTime();
  const tick = () => {
    const now = new Date();
    timeEl.textContent = now.toLocaleTimeString(undefined, {
      hour: "numeric",
      minute: "2-digit",
      second: "2-digit",
      hour12: true,
    });
    dateEl.textContent = now.toLocaleDateString(undefined, {
      month: "long",
      day: "numeric",
      year: "numeric",
    });
  };
  tick();
  veraHeaderDateTimeTimer = setInterval(tick, 1000);
}

/** Clock pill is work-mode only; stops the interval when leaving work mode. */
function syncVeraHeaderDateTimeForWorkMode() {
  const work = document.getElementById("vera-app")?.classList.contains("work-mode");
  if (!work) {
    stopVeraHeaderDateTime();
    return;
  }
  wireVeraHeaderDateTime();
}

window.syncVeraHeaderDateTimeForWorkMode = syncVeraHeaderDateTimeForWorkMode;

function onSidePaneClick(event) {
  const target = event.target;
  if (target instanceof HTMLElement && target.closest(".side-pane-close")) {
    hideSidePanel();
    return;
  }

  if (target instanceof HTMLElement) {
    const tabButton = target.closest(".side-pane-tab");
    if (tabButton instanceof HTMLButtonElement) {
      setActiveSidePaneTab(tabButton.dataset.tab || "news");
    }
  }
}

["vera-side-pane", "bmo-side-pane"].forEach((id) => {
  document.getElementById(id)?.addEventListener("click", onSidePaneClick);
});

function isFlowModeSidePaneCrossfadeEnabled() {
  try {
    if (appModePrefix() === "vera" && document.getElementById("vera-app")?.classList.contains("work-mode")) {
      return false;
    }
  } catch {}
  return true;
}

/**
 * When the side pane is already visible, swap inner content with a short fade (music ↔ news / finance)
 * so innerHTML replacement does not fight the panel slide-in transition.
 */
function runFlowModeSidePaneContentCrossfade(sidePaneEl, renderCallback) {
  if (
    !sidePaneEl ||
    !isFlowModeSidePaneCrossfadeEnabled() ||
    sidePaneEl.hidden ||
    !sidePaneEl.classList.contains("visible")
  ) {
    renderCallback();
    return;
  }

  let outDone = false;
  let fallbackOut = null;
  const finishOut = () => {
    if (outDone) return;
    outDone = true;
    if (fallbackOut != null) window.clearTimeout(fallbackOut);
    sidePaneEl.removeEventListener("transitionend", onOutEnd);
    renderCallback();
    window.requestAnimationFrame(() => {
      sidePaneEl.classList.remove("side-pane-swap-hiding");
      sidePaneEl.classList.add("side-pane-swap-in");
      let fallbackIn = null;
      function clearIn() {
        if (fallbackIn != null) window.clearTimeout(fallbackIn);
        sidePaneEl.removeEventListener("animationend", onInEnd);
        sidePaneEl.classList.remove("side-pane-swap-in");
      }
      function onInEnd(ev) {
        const n = String(ev.animationName || "");
        if (!n.includes("side-pane-content-swap-in")) return;
        clearIn();
      }
      sidePaneEl.addEventListener("animationend", onInEnd);
      fallbackIn = window.setTimeout(clearIn, 480);
    });
  };

  const onOutEnd = (ev) => {
    if (ev.target !== sidePaneEl) return;
    if (ev.propertyName !== "opacity" && ev.propertyName !== "filter") return;
    finishOut();
  };

  sidePaneEl.classList.add("side-pane-swap-hiding");
  sidePaneEl.addEventListener("transitionend", onOutEnd);
  fallbackOut = window.setTimeout(finishOut, 420);
}

/** NDJSON can call ``applyActionPayload`` from ``finalizeNdjsonStreamingReply`` before first audio and again from ``onPlayStart`` — duplicate Spotify starts twitch the UI. */
function musicPlaybackDedupeKey(payload, op) {
  if (!payload || payload.panel_type !== "music_control") return "";
  if (op === "play_track" && payload.uri) return `play_track:${String(payload.uri).trim()}`;
  if (op === "play_album" && payload.uri) return `play_album:${String(payload.uri).trim()}`;
  if (op === "play_playlist_by_name") {
    const n = String(payload.playlist_name || "").trim().toLowerCase();
    if (n) return `play_playlist_by_name:${n}`;
  }
  return "";
}

function isRecentSameMusicPlay(payload, op) {
  const key = musicPlaybackDedupeKey(payload, op);
  if (!key) return false;
  const prev = window.__veraMusicPlaybackDedupe;
  return !!(prev && prev.key === key && performance.now() - prev.at < 7000);
}

/** Returns false when the same play was already started a few seconds ago (NDJSON finalize + first-audio both call this). */
function shouldPlayMusicThisInvocation(payload, op) {
  const key = musicPlaybackDedupeKey(payload, op);
  if (!key) return true;
  const now = performance.now();
  const prev = window.__veraMusicPlaybackDedupe;
  if (prev && prev.key === key && now - prev.at < 7000) return false;
  window.__veraMusicPlaybackDedupe = { key, at: now };
  return true;
}

function applyActionPayload(data) {
  const payload = data?.action_payload;
  const lockToMusicPanel =
    isVeraWorkModeOn() && appModePrefix() === "vera";

  if (
    lockToMusicPanel &&
    (payload?.panel_type === "media_tabs" ||
      payload?.panel_type === "news_results" ||
      payload?.panel_type === "finance_chart")
  ) {
    const sidePaneEl = uiEl("side-pane");
    if (sidePaneEl) {
      const hasProductivityMarkup =
        Boolean(sidePaneEl.innerHTML.trim()) && sidePaneEl.dataset.sidePaneKind === "productivity";
      if (hasProductivityMarkup) {
        if (sidePaneEl.hidden) restoreProductivityPanel("vera");
      } else {
        renderProductivityPanel();
      }
    }
    return;
  }

  if (payload?.panel_type === "media_tabs" || payload?.panel_type === "news_results") {
    /* Large innerHTML (news + images + video embeds) can block the main thread; defer so BMO mouth RAF keeps up. */
    requestAnimationFrame(() => renderMediaTabsPanel(payload));
    return;
  }

  if (payload?.panel_type === "finance_chart") {
    renderFinanceChartPanel(payload);
    return;
  }

  if (payload?.panel_type === "checklist_control") {
    try {
      markWorkChecklistLocalMutation();
      if (Array.isArray(payload.items)) {
        localStorage.setItem(WORK_CHECKLIST_STORAGE_KEY, JSON.stringify(payload.items));
      }
      if (typeof payload.completed_collapsed === "boolean") {
        localStorage.setItem(
          WORK_CHECKLIST_COMPLETED_COLLAPSED_KEY,
          payload.completed_collapsed ? "1" : "0"
        );
      }
      loadWorkChecklistItems();
      syncWorkChecklistHelpPlanButton();
    } catch (_) {}
    return;
  }

  if (payload?.panel_type === "music_control") {
    const prefix = appModePrefix();
    const op = payload.op || "open_panel";
    if (op === "close_panel") {
      hideSidePanel();
      return;
    }
    if (op === "pause") {
      const pause = window.VeraSpotify?.pausePlayback;
      if (typeof pause === "function") void pause();
      return;
    }
    if (op === "resume") {
      const resume = window.VeraSpotify?.resumePlayback;
      if (typeof resume === "function") void resume();
      return;
    }
    if (op === "volume_delta") {
      const cur = typeof window.VeraSpotify?.getVolume === "function"
        ? window.VeraSpotify.getVolume()
        : spotifyGetVolume();
      const setVolume = window.VeraSpotify?.setVolume;
      const next = Math.max(0, Math.min(SPOTIFY_VOLUME_MAX, Number(cur) + (Number(payload.delta) || 0)));
      if (typeof setVolume === "function") void setVolume(next);
      return;
    }
    const skipPanelRepeat = isRecentSameMusicPlay(payload, op);
    const sidePaneEl = uiEl("side-pane");
    if (sidePaneEl && !skipPanelRepeat) {
      const hasProductivityMarkup =
        Boolean(sidePaneEl.innerHTML.trim()) && sidePaneEl.dataset.sidePaneKind === "productivity";
      document.querySelectorAll(".productivity-mode-btn").forEach((b) => b.classList.remove("is-active"));
      if (hasProductivityMarkup) {
        if (sidePaneEl.hidden) restoreProductivityPanel(prefix);
      } else {
        renderProductivityPanel();
      }
      document.getElementById(`${prefix}-productivity-mode`)?.classList.add("is-active");
    }
    if (op === "play_track" && payload.uri && shouldPlayMusicThisInvocation(payload, op)) {
      const play = window.VeraSpotify?.playTrack;
      if (typeof play === "function") {
        void play(String(payload.uri), {
          title: payload.title || "",
          artist: payload.artist || "",
          preview_url: payload.preview_url || "",
          open_url: payload.open_url || ""
        });
      }
    } else if (op === "play_album" && payload.uri && shouldPlayMusicThisInvocation(payload, op)) {
      const playCtx = window.VeraSpotify?.playPlaylist;
      if (typeof playCtx === "function") {
        void (async () => {
          const prefix = appModePrefix();
          const base = localBackendBase();
          const uri = String(payload.uri || "").trim();
          const title = payload.title || "";
          const artist = payload.artist || "";
          const sub = artist ? `"${title}" by "${artist}"` : `"${title}"`;
          const openUrl = String(payload.open_url || spotifyUriToOpenUrl(uri) || "").trim();
          const st = await fetch(`${base}/api/spotify/connection-status`, {
            credentials: "include",
            headers: { ...veraSpotifyAuthHeaders() }
          })
            .then((r) => (r.ok ? r.json() : { connected: false }))
            .catch(() => ({ connected: false }));
          const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
          if (st.connected) {
            await playCtx(uri, { playlist_name: title, context_subtitle: sub });
          } else if (openUrl) {
            window.open(openUrl, "_blank", "noopener,noreferrer");
            if (artistEl) {
              artistEl.textContent =
                `${artist ? `${artist} — ` : ""}Opened Spotify in a new tab (connect for in-page playback).`.trim();
            }
          } else if (artistEl) {
            artistEl.textContent = "Connect Spotify to play this album in VERA.";
          }
        })();
      }
    } else if (op === "play_playlist_by_name") {
      const rawName = String(payload.playlist_name || "").trim();
      if (rawName && shouldPlayMusicThisInvocation(payload, op)) {
        void (async () => {
          const prefix = appModePrefix();
          const getLists = window.VeraSpotify?.getPlaylists;
          const playCtx = window.VeraSpotify?.playPlaylist;
          const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
          if (typeof getLists !== "function" || typeof playCtx !== "function") {
            if (artistEl) artistEl.textContent = "Playlist playback is not available.";
            return;
          }
          const lists = await getLists().catch(() => []);
          const needle = rawName.toLowerCase();
          let hit =
            lists.find((p) => String(p.name || "").toLowerCase() === needle) ||
            lists.find((p) => String(p.name || "").toLowerCase().includes(needle));
          if (!hit && needle.length >= 3) {
            hit = lists.find((p) => needle.includes(String(p.name || "").toLowerCase()));
          }
          if (!hit?.uri) {
            if (artistEl) artistEl.textContent = `No playlist in your library matched "${rawName}".`;
            return;
          }
          const disp = hit.name || rawName;
          await playCtx(hit.uri, {
            playlist_name: disp,
            context_subtitle: `"${disp}" in my playlist`
          });
        })();
      }
    }
    return;
  }

  /* Keep the music panel open across normal assistant replies unless a new panel payload replaces it. */
  const sidePaneEl = uiEl("side-pane");
  if (
    sidePaneEl &&
    !sidePaneEl.hidden &&
    sidePaneEl.dataset.sidePaneKind === "productivity"
  ) {
    return;
  }

  hideSidePanel();
}

/** News/finance side panel + assistant bubble — call when main reply audio actually starts (not when LLM JSON/meta arrives). */
function applyAssistantReplyAndPanels(data) {
  if (!data) return;
  applyActionPayload(data);
  if (data.reply == null || data.reply === "") return;
  addBubble(data.reply, "vera");
}

function createNdjsonStreamingReplyState() {
  return { bubble: null, latest: "" };
}

/**
 * Grow one assistant bubble as each NDJSON chunk includes reply_so_far (sentence-cumulative text).
 */
function applyNdjsonStreamingReplySoFar(replySoFar, state) {
  if (replySoFar == null || replySoFar === "") return;
  state.latest = String(replySoFar);
  const convoEl = uiEl("conversation");
  if (!convoEl) return;
  const text = state.latest;
  if (state.bubble?.isConnected) {
    const cur = state.bubble.textContent || "";
    /* Done line can arrive before deferred first play; finalize may have filled the full reply — don't overwrite with a shorter cumulative partial. */
    if (text.length >= cur.length) {
      state.bubble.textContent = text;
    }
  } else {
    state.bubble = addBubble(text, "vera", { path: "ndjson-reply-so-far" });
  }
  convoEl.scrollTop = convoEl.scrollHeight;
  persistVeraChatState();
}

/** After NDJSON done: sync bubble to final reply, or add bubble if no streaming partials. */
function finalizeNdjsonStreamingReply(ndjsonMeta, done, state) {
  if (!done?.reply) return;
  if (state.bubble?.isConnected) {
    state.bubble.textContent = done.reply;
    persistVeraChatState();
    return;
  }
  /* Must assign state.bubble so applyNdjsonStreamingReplySoFar doesn't add a second bubble if done arrives before first audio (defer path). */
  applyActionPayload({ ...ndjsonMeta, reply: done.reply });
  state.bubble = addBubble(done.reply, "vera", { path: "ndjson-final" });
  persistVeraChatState();
}

/** Stops TTS and resets interrupt UI counters (shared by heuristic + browser barge-in). */
function cancelBrowserInterruptTtsOnly() {
  setStatus("Listening… (interrupted)", "recording");
  resetAudioHandlers();
  cancelMainTtsPlayback();
  const a = getAudioEl();
  if (a) {
    a.pause();
    a.currentTime = 0;
  }
  listening = true;
  processing = false;
  waveState = "listening";
  interruptSpeechFrames = 0;
  interruptSpeechStart = 0;
  interruptSpeechAccumMs = 0;
  lastInterruptDetectTime = 0;
  interruptLastSpeechLikeTime = 0;
  lastInterruptSpeechLikeSnapshot = null;
  interruptLastVoiceTime = performance.now();
}

function promoteInterruptPreviewToMainLiveBubble() {
  if (interruptDetectionBubbleEl?.isConnected) {
    mainBrowserLiveBubble = interruptDetectionBubbleEl;
    interruptDetectionBubbleEl = null;
    try {
      mainBrowserLiveBubble.classList.remove("interrupt-preview");
    } catch (_) {}
  }
}

/**
 * Browser ASR: >2 words ⇒ stop TTS; keep the same SpeechRecognition session and use 1.3s stable transcript → LLM.
 * (Does not start a second recognition — that was the old post-interrupt listener.)
 */
function onBrowserInterruptBargeInFromDetect(event) {
  if (interruptBargeInLatched) return;
  interruptBargeInLatched = true;
  cancelBrowserInterruptTtsOnly();
  promoteInterruptPreviewToMainLiveBubble();
  mainBrowserFinalizeKind = "interrupt";

  let interimBuf = "";
  let finalP = "";
  for (let i = 0; i < event.results.length; i++) {
    const r = event.results[i];
    if (r.isFinal) {
      const piece = r[0].transcript;
      finalP += piece;
      logPartialAsrSegmentFinal(piece.trim(), { mode: "interrupt-barge" });
    } else {
      interimBuf += r[0].transcript;
    }
  }
  mainBrowserFinalTranscript = finalP;
  mainBrowserLastInterim = interimBuf;
  hasSpoken =
    mainBrowserFinalTranscript.trim().length > 0 || interimBuf.trim().length > 0;
  if (hasSpoken && speechWaitTimeoutId != null) {
    clearTimeout(speechWaitTimeoutId);
    speechWaitTimeoutId = null;
  }
  updateMainBrowserLiveBubble(mainBrowserFinalTranscript, interimBuf);
  scheduleMainBrowserEndOfUtterance();
}

function interruptSpeech() {
  if (listeningMode !== "continuous") return;
  const useBrowserAsr = browserAsrPreferred();
  if (!interruptRecording && !useBrowserAsr) return;
  const a = getAudioEl();
  const htmlPlaying = a && !a.paused;
  const webTtsPlaying =
    activeMainTtsBufferSources.length > 0 || mainTtsPlaybackActive;
  if (!htmlPlaying && !webTtsPlaying) return;

  cancelBrowserInterruptTtsOnly();

  if (interruptRecording) {
    requestAnimationFrame(detectInterruptSpeechEnd);
  } else if (useBrowserAsr) {
    /* No MediaRecorder interrupt path: start dedicated post-interrupt SR (e.g. phone Chrome edge cases). */
    promoteInterruptPreviewToMainLiveBubble();
    startPostInterruptBrowserRecognition();
  }
}

function detectInterrupt() {
  if (!analyser) {
    requestAnimationFrame(detectInterrupt);
    return;
  }

  /*
   * Desktop + browser ASR: while interrupt-detect SpeechRecognition is alive, barge-in is word-count only.
   * If start() failed or onend fired, fall back to heuristic so TTS is still interruptible (no silent failure).
   */
  if (
    browserAsrPreferred() &&
    !isNarrowViewport() &&
    interruptDetectRecognition
  ) {
    requestAnimationFrame(detectInterrupt);
    return;
  }

  const buf = new Float32Array(analyser.fftSize);
  analyser.getFloatTimeDomainData(buf);

  // RMS
  let sum = 0;
  for (let i = 0; i < buf.length; i++) sum += buf[i] * buf[i];
  const rms = Math.sqrt(sum / buf.length);

  // ZCR (voicing) + crest (reject single sharp transients from bumps/clicks)
  const zcr = computeZCR(buf);
  let peak = 0;
  for (let i = 0; i < buf.length; i++) {
    const a = Math.abs(buf[i]);
    if (a > peak) peak = a;
  }
  const crest = peak / (rms + 1e-8);

  const now = performance.now();

  // Only interrupt while main TTS is playing: single-file uses <audio>; chunked/streaming uses Web Audio BufferSources.
  const outAudio = getAudioEl();
  const htmlAudioPlaying = outAudio && !outAudio.paused;
  const webAudioMainTtsPlaying =
    activeMainTtsBufferSources.length > 0 || mainTtsPlaybackActive;
  if (
  listeningMode === "continuous" &&
  (htmlAudioPlaying || webAudioMainTtsPlaying)
) {
    // grace period to avoid clicks
    if (now - audioStartedAt > 200) {
      const dtRaw = lastInterruptDetectTime ? now - lastInterruptDetectTime : 0;
      const dt = Math.min(Math.max(dtRaw, 0), 80);
      lastInterruptDetectTime = now;

      const heuristicChecks = computeHeuristicInterruptChecks(rms, zcr, crest);
      const speechLike = heuristicChecks.passes;

      if (speechLike) {
        interruptSpeechAccumMs += dt;
        if (interruptSpeechFrames === 0) {
          interruptSpeechStart = now;
        }
        interruptSpeechFrames++;
        interruptLastSpeechLikeTime = now;
        lastInterruptSpeechLikeSnapshot = {
          rms,
          zcr,
          crest,
          heuristicChecks,
          at: now,
        };
      } else if (
        interruptLastSpeechLikeTime &&
        now - interruptLastSpeechLikeTime <= INTERRUPT_GAP_RESET_MS
      ) {
        // Allow tiny gaps so normal speech doesn't need a perfect uninterrupted stream (time here does not add to interruptSpeechAccumMs).
      } else {
        interruptSpeechFrames = 0;
        interruptSpeechStart = 0;
        interruptSpeechAccumMs = 0;
        interruptLastSpeechLikeTime = 0;
        lastInterruptSpeechLikeSnapshot = null;
      }

      if (
        speechLike &&
        interruptSpeechFrames >= INTERRUPT_MIN_FRAMES &&
        interruptSpeechAccumMs >= getInterruptSustainMs()
      ) {
        const gate = "heuristic";
        const snap = lastInterruptSpeechLikeSnapshot;
        logInterruptTriggerReason({
          gate,
          triggerFrame: { rms, zcr, crest, speechLike },
          lastSpeechLike: snap,
          speechAccumMs: interruptSpeechAccumMs,
          wallMsSinceFirstSpeech: interruptSpeechStart
            ? now - interruptSpeechStart
            : 0,
          rafFrames: interruptSpeechFrames,
        });
        lastInterruptProbe = {
          atTrigger: { rms, zcr, crest, speechLike },
          lastSpeechLike: snap,
          interruptGate: gate,
          interruptReason: "heuristic",
          heuristicChecks: snap?.heuristicChecks ?? heuristicChecks,
          speechAccumMs: interruptSpeechAccumMs,
          wallMsSinceFirstSpeech: interruptSpeechStart
            ? now - interruptSpeechStart
            : 0,
          frames: interruptSpeechFrames,
        };
        interruptSpeech();
        interruptSpeechFrames = 0;
        interruptSpeechStart = 0;
        interruptSpeechAccumMs = 0;
        interruptLastSpeechLikeTime = 0;
        lastInterruptSpeechLikeSnapshot = null;
      }

      if (
        MOBILE_VAD_DEBUG &&
        now - lastMobileVadSampleLogAt >= MOBILE_VAD_SAMPLE_INTERVAL_MS
      ) {
        lastMobileVadSampleLogAt = now;
        pushMobileInterruptVadLog(
          `vad rms=${rms.toFixed(4)} zcr=${zcr.toFixed(4)} crest=${crest.toFixed(2)} like=${speechLike} acc=${interruptSpeechAccumMs.toFixed(0)}ms thr=${getInterruptSustainMs()}ms`
        );
      }
    }
  } else {
    interruptSpeechFrames = 0;
    interruptSpeechStart = 0;
    interruptSpeechAccumMs = 0;
    lastInterruptDetectTime = 0;
    interruptLastSpeechLikeTime = 0;
    lastInterruptSpeechLikeSnapshot = null;
  }

  requestAnimationFrame(detectInterrupt);
}

function resetAudioHandlers() {
  const a = getAudioEl();
  if (a) {
    a.onplay = null;
    a.onended = null;
  }
}

let interruptLastVoiceTime = 0;

function detectInterruptSpeechEnd() {
  if (!interruptRecording || interruptRecorder?.state !== "recording") return;

  const buf = new Float32Array(analyser.fftSize);
  analyser.getFloatTimeDomainData(buf);

  let sum = 0;
  for (let i = 0; i < buf.length; i++) sum += buf[i] * buf[i];
  const rms = Math.sqrt(sum / buf.length);

  const now = performance.now();

  if (listeningFrameIsSpeechLike(buf, rms)) {
    interruptLastVoiceTime = now;
  }

  if (
    interruptLastVoiceTime &&
    now - interruptLastVoiceTime > SILENCE_MS
  ) {
    interruptRecorder.stop(); // ✅ NOW stop
    interruptRecording = false;
    return;
  }

  requestAnimationFrame(detectInterruptSpeechEnd);
}

function computeZCR(buf) {
  let crossings = 0;
  for (let i = 1; i < buf.length; i++) {
    if ((buf[i - 1] >= 0 && buf[i] < 0) ||
        (buf[i - 1] < 0 && buf[i] >= 0)) {
      crossings++;
    }
  }
  return crossings / buf.length;
}

/** RMS + ZCR voiced band — used so background noise alone does not stall end-of-speech. */
function listeningFrameIsSpeechLike(buf, rms) {
  const zcr = computeZCR(buf);
  if (IS_MOBILE) {
    /* Phone mics (Bluetooth, handset, AGC off) are often quieter and ZCR sits outside desktop bands. */
    const th = VOLUME_THRESHOLD * 0.55;
    if (rms <= th) return false;
    const zLo = LISTEN_END_ZCR_MIN * 0.55;
    const zHi = Math.min(0.28, LISTEN_END_ZCR_MAX * 1.35);
    return zcr >= zLo && zcr <= zHi;
  }
  if (rms <= VOLUME_THRESHOLD) return false;
  return zcr >= LISTEN_END_ZCR_MIN && zcr <= LISTEN_END_ZCR_MAX;
}

/** Per-threshold flags for interrupt (RMS/ZCR/crest); all must pass for a frame to count as speech-like. */
function computeHeuristicInterruptChecks(rms, zcr, crest) {
  const rmsAboveMin = rms > INTERRUPT_RMS;
  const rmsBelowMax = rms < MAX_SPEECH_RMS;
  const zcrInRange = zcr >= INTERRUPT_ZCR_MIN && zcr <= INTERRUPT_ZCR_MAX;
  const crestOk = crest <= INTERRUPT_MAX_CREST;
  return {
    rmsAboveMin,
    rmsBelowMax,
    zcrInRange,
    crestOk,
    passes:
      rmsAboveMin && rmsBelowMax && zcrInRange && crestOk,
  };
}

function logInterruptTriggerReason({
  gate,
  triggerFrame,
  lastSpeechLike,
  speechAccumMs,
  wallMsSinceFirstSpeech,
  rafFrames,
}) {
  const base = {
    gate,
    speechAccumMs: Number(speechAccumMs.toFixed(1)),
    wallMsSinceFirstSpeech: Number(wallMsSinceFirstSpeech.toFixed(1)),
    rafFrames,
    triggerKind: `speech_frame (accumulated speechLike time ≥ ${getInterruptSustainMs()}ms)`,
    triggerFrame: {
      rms: Number(triggerFrame.rms.toFixed(5)),
      zcr: Number(triggerFrame.zcr.toFixed(5)),
      crest: Number(triggerFrame.crest.toFixed(4)),
      speechLike: triggerFrame.speechLike,
    },
  };
  const h =
    lastSpeechLike?.heuristicChecks ??
    computeHeuristicInterruptChecks(
      lastSpeechLike?.rms ?? triggerFrame.rms,
      lastSpeechLike?.zcr ?? triggerFrame.zcr,
      lastSpeechLike?.crest ?? triggerFrame.crest
    );
  const checks = [];
  if (h.rmsAboveMin) checks.push("rms_min");
  if (h.rmsBelowMax) checks.push("rms_max");
  if (h.zcrInRange) checks.push("zcr");
  if (h.crestOk) checks.push("crest");
  console.log(
    "[INTERRUPT] trigger — heuristic (RMS/ZCR/crest + sustain; all must pass on speech frames)",
    {
      ...base,
      lastSpeechLike: lastSpeechLike
        ? {
            rms: Number(lastSpeechLike.rms.toFixed(5)),
            zcr: Number(lastSpeechLike.zcr.toFixed(5)),
            crest: Number(lastSpeechLike.crest.toFixed(4)),
            heuristicChecks: checks.join("+"),
            flags: {
              rmsAboveMin: h.rmsAboveMin,
              rmsBelowMax: h.rmsBelowMax,
              zcrInRange: h.zcrInRange,
              crestOk: h.crestOk,
            },
          }
        : null,
    }
  );
  pushMobileInterruptVadLog(
    `[INTERRUPT] gate=${gate} accumMs=${speechAccumMs.toFixed(1)} rms=${triggerFrame.rms.toFixed(5)} zcr=${triggerFrame.zcr.toFixed(5)} crest=${triggerFrame.crest.toFixed(4)} checks=${checks.join("+")}`
  );
}

function pushMobileInterruptVadLog(msg) {
  if (!MOBILE_VAD_DEBUG) return;
  const t = new Date().toISOString().slice(11, 23);
  interruptVadLogLines.push(`[${t}] ${msg}`);
  if (interruptVadLogLines.length > INTERRUPT_VAD_LOG_MAX) {
    interruptVadLogLines.splice(0, interruptVadLogLines.length - INTERRUPT_VAD_LOG_MAX);
  }
  renderMobileInterruptVadLogs();
}

function renderMobileInterruptVadLogs() {
  const text = interruptVadLogLines.join("\n");
  const p1 = document.getElementById("vera-interrupt-debug-pre");
  const p2 = document.getElementById("bmo-interrupt-debug-pre");
  if (p1) p1.textContent = text;
  if (p2) p2.textContent = text;
}

function toggleInterruptDebugPanel(prefix) {
  const panel = document.getElementById(`${prefix}-interrupt-debug-panel`);
  const btn = document.getElementById(`${prefix}-interrupt-debug-toggle`);
  const headerBtn = document.getElementById(`${prefix}-interrupt-debug-header`);
  if (!panel) return;
  const opening = panel.hidden;
  panel.hidden = !opening;
  const expanded = opening ? "true" : "false";
  btn?.setAttribute("aria-expanded", expanded);
  headerBtn?.setAttribute("aria-expanded", expanded);
  if (opening) {
    requestAnimationFrame(() => {
      panel.scrollIntoView({ block: "end", behavior: "smooth" });
    });
  }
}

function injectMobileVadLogUiIfNeeded() {
  if (!MOBILE_VAD_DEBUG) return;
  document.body.classList.add("vad-log-mode");

  const veraHeader = document.querySelector("#vera-app .vera-app-header");
  const veraOpenBmo = document.getElementById("open-bmo-from-vera");
  if (veraHeader && veraOpenBmo && !document.getElementById("vera-interrupt-debug-header")) {
    const wrap = document.createElement("div");
    wrap.className = "vera-header-actions";
    const vadBtn = document.createElement("button");
    vadBtn.type = "button";
    vadBtn.id = "vera-interrupt-debug-header";
    vadBtn.className = "interrupt-debug-header-btn";
    vadBtn.setAttribute("aria-controls", "vera-interrupt-debug-panel");
    vadBtn.textContent = "VAD log";
    veraOpenBmo.parentNode.insertBefore(wrap, veraOpenBmo);
    wrap.appendChild(vadBtn);
    wrap.appendChild(veraOpenBmo);
  }

  const bmoHeader = document.querySelector("#bmo-page .bmo-chat-header");
  if (bmoHeader && !document.getElementById("bmo-interrupt-debug-header")) {
    const vadBtn = document.createElement("button");
    vadBtn.type = "button";
    vadBtn.id = "bmo-interrupt-debug-header";
    vadBtn.className = "interrupt-debug-header-btn";
    vadBtn.setAttribute("aria-controls", "bmo-interrupt-debug-panel");
    vadBtn.textContent = "VAD log";
    bmoHeader.appendChild(vadBtn);
  }

  function buildExtender(prefix) {
    const wrap = document.createElement("div");
    wrap.className = "interrupt-debug-extender";
    const toggle = document.createElement("button");
    toggle.type = "button";
    toggle.id = `${prefix}-interrupt-debug-toggle`;
    toggle.className = "interrupt-debug-toggle";
    toggle.setAttribute("aria-expanded", "false");
    toggle.setAttribute("aria-controls", `${prefix}-interrupt-debug-panel`);
    toggle.textContent = "Interrupt / VAD log";
    const panel = document.createElement("div");
    panel.id = `${prefix}-interrupt-debug-panel`;
    panel.className = "interrupt-debug-panel";
    panel.hidden = true;
    const pre = document.createElement("pre");
    pre.id = `${prefix}-interrupt-debug-pre`;
    pre.className = "interrupt-debug-pre";
    pre.setAttribute("aria-live", "polite");
    const clearBtn = document.createElement("button");
    clearBtn.type = "button";
    clearBtn.id = `${prefix}-interrupt-debug-clear`;
    clearBtn.className = "interrupt-debug-clear";
    clearBtn.textContent = "Clear";
    panel.appendChild(pre);
    panel.appendChild(clearBtn);
    wrap.appendChild(toggle);
    wrap.appendChild(panel);
    return wrap;
  }

  const veraIc = document.querySelector("#vera-app .input-container");
  if (veraIc && !document.getElementById("vera-interrupt-debug-panel")) {
    veraIc.appendChild(buildExtender("vera"));
  }

  const bmoIc = document.querySelector("#bmo-page .input-container");
  if (bmoIc && !document.getElementById("bmo-interrupt-debug-panel")) {
    bmoIc.appendChild(buildExtender("bmo"));
  }
}

function wireMobileInterruptDebugUi() {
  if (!MOBILE_VAD_DEBUG) return;
  injectMobileVadLogUiIfNeeded();
  pushMobileInterruptVadLog(
    `sustain=${getInterruptSustainMs()}ms (${INTERRUPT_SUSTAIN_MS_PHONE}ms phone / ${INTERRUPT_SUSTAIN_MS_DESKTOP}ms desktop viewport)`
  );
  ["vera", "bmo"].forEach((prefix) => {
    const btn = document.getElementById(`${prefix}-interrupt-debug-toggle`);
    const headerBtn = document.getElementById(`${prefix}-interrupt-debug-header`);
    const panel = document.getElementById(`${prefix}-interrupt-debug-panel`);
    const clearBtn = document.getElementById(`${prefix}-interrupt-debug-clear`);
    if (!panel) return;
    const toggle = () => toggleInterruptDebugPanel(prefix);
    btn?.addEventListener("click", toggle);
    headerBtn?.addEventListener("click", toggle);
    clearBtn?.addEventListener("click", (e) => {
      e.preventDefault();
      e.stopPropagation();
      interruptVadLogLines.length = 0;
      renderMobileInterruptVadLogs();
    });
  });
}

function startInterruptCapture() {
  if (listeningMode !== "continuous") {
    interruptRecording = false;
    interruptChunks = [];
    return;
  }
  if (browserAsrPreferred() && !isNarrowViewport()) {
    startInterruptBrowserPartialDetection();
    return;
  }

  // 🔥 HARD FLUSH — stop and discard any previous capture
  if (interruptRecorder && interruptRecorder.state !== "inactive") {
    try {
      interruptRecorder.ondataavailable = null;
      interruptRecorder.onstop = null;
      interruptRecorder.stop();
    } catch {}
  }

  interruptRecorder = null;
  interruptRecording = false;
  interruptChunks = [];
  interruptSpeechFrames = 0;
  interruptSpeechStart = 0;
  interruptSpeechAccumMs = 0;
  lastInterruptDetectTime = 0;
  interruptLastSpeechLikeTime = 0;
  lastInterruptSpeechLikeSnapshot = null;

  // ---------- START FRESH RECORDER ----------
  interruptRecorder = new MediaRecorder(micStream);

  interruptRecorder.ondataavailable = (e) => {
    if (e.data && e.data.size > 0) {
      interruptChunks.push(e.data);
    }
  };

  interruptRecorder.onstop = () => {
    const blob = new Blob(interruptChunks, { type: "audio/webm" });

    interruptRecorder = null;
    interruptRecording = false;
    interruptChunks = [];

    handleInterruptUtterance(blob);
  };

  interruptRecorder.start();   // 🚀 clean segment start
  interruptRecording = true;
}

async function handleInterruptUtterance(blob) {
  if (blob.size < MIN_AUDIO_BYTES) {
    listening = true;
    return;
  }

  requestInFlight = true;
  processing = true;
  waveState = "idle";
  setStatus("Thinking", "thinking");

  const formData = new FormData();
  formData.append("audio", blob);
  formData.append("session_id", getSessionId());
  formData.append("client", appModePrefix());
  formData.append("context_snapshot", JSON.stringify(buildClientContextSnapshot()));
  formData.append("mode", "interrupt"); // backend can branch if desired
  formData.append(
    "interrupt_debug",
    JSON.stringify({
      probe: lastInterruptProbe,
      thresholds: {
        INTERRUPT_RMS,
        INTERRUPT_ZCR_MIN,
        INTERRUPT_ZCR_MAX,
        INTERRUPT_SUSTAIN_MS: getInterruptSustainMs(),
        INTERRUPT_GAP_RESET_MS,
        INTERRUPT_MAX_CREST,
        MAX_SPEECH_RMS,
      },
    })
  );
  formData.append("stream_tts", shouldStreamTts() ? "1" : "0");

  await runInferInterruptPipeline(formData);
}

async function playInterruptAnswer(data) {
  const run = async () => {
    resetAudioHandlers();
    try {
      await playTtsFromApi(data, {
        onPlayStart: () => {
          logVoiceFirstAudio("main-reply");
          logVoiceMainReplyAudio();
          applyAssistantReplyAndPanels(data);
          waveState = "speaking";
          audioStartedAt = performance.now();
          setStatus("Speaking… (can only be interrupted once)", "speaking");
          processing = false;
        },
        onPlayEnd: () => {
          resumeListeningAfterInterruptPlayback();
        }
      });
    } catch (e) {
      console.warn(e);
    }
  };

  await run();
}
/* =========================
   MIC INIT
========================= */

/** Per-mode TTS <audio> through Web Audio (vera-audio / bmo-audio). */
async function ensureMainAudioTtsGraph() {
  const m = appModePrefix();
  const el = getAudioEl();
  if (!el || ttsByMode[m].source) return;
  if (!audioCtx) {
    audioCtx = new AudioContext({ sampleRate: 16000 });
  }
  await audioCtx.resume();
  const analyser = audioCtx.createAnalyser();
  analyser.fftSize = 2048;
  const gain = audioCtx.createGain();
  gain.gain.value = 1;
  const source = audioCtx.createMediaElementSource(el);
  source.connect(analyser);
  source.connect(gain);
  gain.connect(audioCtx.destination);
  ttsByMode[m].source = source;
  ttsByMode[m].analyser = analyser;
  ttsByMode[m].gain = gain;
  applyVeraWorkModeMuteSetting();
}

/** Prefer `audio_urls` when present (sentence-chunked TTS); else single `audio_url`. */
function resolveAudioUrls(data) {
  if (Array.isArray(data.audio_urls) && data.audio_urls.length) return data.audio_urls;
  if (data.audio_url) return [data.audio_url];
  return [];
}

/** Sentence-chunk / streaming TTS uses BufferSource → destination; `<audio>` stays paused, so interrupt must track these. */
let activeMainTtsBufferSources = [];
/** True from first main TTS chunk until last chunk ends — gaps between BufferSources have 0 active sources but TTS is still "playing". */
let mainTtsPlaybackActive = false;

function isAssistantTtsPlaying() {
  const outAudio = getAudioEl();
  const htmlAudioPlaying = outAudio && !outAudio.paused;
  const webAudioMainTtsPlaying =
    activeMainTtsBufferSources.length > 0 || mainTtsPlaybackActive;
  return Boolean(htmlAudioPlaying || webAudioMainTtsPlaying);
}

/** Incremented on interrupt so NDJSON read + incremental Web Audio loops exit and stop scheduling further chunks. */
let mainTtsPlaybackToken = 0;
/** Active NDJSON `res.body.getReader()`; cancelled on interrupt so the stream stops feeding the URL queue. */
let activeNdjsonBodyReader = null;

function registerMainTtsBufferSource(src, onEndedExtra) {
  activeMainTtsBufferSources.push(src);
  src.onended = () => {
    const i = activeMainTtsBufferSources.indexOf(src);
    if (i >= 0) activeMainTtsBufferSources.splice(i, 1);
    if (onEndedExtra) onEndedExtra();
  };
}

function stopAllMainTtsWebAudio() {
  mainTtsPlaybackActive = false;
  const copy = activeMainTtsBufferSources.slice();
  activeMainTtsBufferSources = [];
  for (const src of copy) {
    try {
      src.onended = null;
      src.stop(0);
    } catch (_) {
      /* already stopped */
    }
  }
  if (document.body.classList.contains("bmo-open")) {
    stopBmoTtsMouthAnimation();
  }
}

function cancelMainTtsPlayback() {
  mainTtsPlaybackToken++;
  stopAllMainTtsWebAudio();
  const r = activeNdjsonBodyReader;
  activeNdjsonBodyReader = null;
  if (r) {
    try {
      r.cancel();
    } catch (_) {
      /* ignore */
    }
  }
}

let activePipelineAbort = null;
let queuedAssistantTtsPlayback = Promise.resolve();

function attachPipelineAbortSignal() {
  activePipelineAbort?.abort();
  activePipelineAbort = new AbortController();
  return activePipelineAbort.signal;
}

function enqueueAssistantTtsPlayback(task) {
  const run = queuedAssistantTtsPlayback
    .catch(() => {})
    .then(async () => {
      await waitUntilAssistantTtsIdle();
      await task();
      await waitUntilAssistantTtsIdle();
    });
  queuedAssistantTtsPlayback = run.catch(() => {});
  return run;
}

async function waitUntilAssistantTtsIdle(maxWaitMs = 60000) {
  const start = performance.now();
  while (isAssistantTtsPlaying()) {
    if (performance.now() - start > maxWaitMs) break;
    await new Promise((resolve) => window.setTimeout(resolve, 40));
  }
}

async function waitForAssistantPlaybackEnd(onFinishHook) {
  let done = false;
  let resolveDone;
  const donePromise = new Promise((resolve) => {
    resolveDone = resolve;
  });
  const finishDone = () => {
    if (done) return;
    done = true;
    resolveDone?.();
  };
  const wrappedOnFinish = () => {
    try {
      if (typeof onFinishHook === "function") onFinishHook();
    } finally {
      finishDone();
    }
  };
  // Safety timeout in case a browser event is missed.
  const timeoutId = window.setTimeout(finishDone, 45000);
  return {
    wrappedOnFinish,
    donePromise: donePromise.finally(() => window.clearTimeout(timeoutId))
  };
}

function isMainTtsOrHtmlAudioPlaying() {
  const a = getAudioEl();
  const htmlPlaying = a && !a.paused;
  const webTts =
    activeMainTtsBufferSources.length > 0 || mainTtsPlaybackActive;
  return htmlPlaying || webTts;
}

function isServerPipelineBusy() {
  return (
    requestInFlight ||
    processing ||
    isMainTtsOrHtmlAudioPlaying()
  );
}

/** Typed send (flow or work mode) can replace an in-flight reply / speaking TTS. */
function isFlowModeKeyboardInterruptAllowed() {
  return true;
}

/** Abort fetch + stop main TTS so the next `/text` send can proceed (keyboard barge-in). */
function interruptAssistantPipelineForTypedMessage() {
  activePipelineAbort?.abort();
  activePipelineAbort = null;
  cancelMainTtsPlayback();
  resetAudioHandlers();
  const a = getAudioEl();
  if (a) {
    a.pause();
    a.currentTime = 0;
  }
  processing = false;
  requestInFlight = false;
  clearInterruptDetectionBubble();
  interruptBargeInLatched = false;
  voiceUxTurn = null;
  textUxTurn = null;
  if (listeningMode === "ptt") {
    listening = false;
    pttRecording = false;
    waveState = "idle";
    setStatus("Ready", "idle");
  } else {
    listening = true;
    waveState = "listening";
    if (inputMuted) showMutedStatusIfIdle();
    else setStatus("Listening…", "recording");
  }
  updateMuteInputButton();
}

function cancelVoicePipelineAndResetState() {
  activePipelineAbort?.abort();
  activePipelineAbort = null;
  cancelMainTtsPlayback();
  resetAudioHandlers();
  const a = getAudioEl();
  if (a) {
    a.pause();
    a.removeAttribute("src");
    a.load?.();
  }
  if (rafId) {
    cancelAnimationFrame(rafId);
    rafId = null;
  }
  if (speechWaitTimeoutId != null) {
    clearTimeout(speechWaitTimeoutId);
    speechWaitTimeoutId = null;
  }
  if (interruptRecorder && interruptRecorder.state !== "inactive") {
    try {
      interruptRecorder.ondataavailable = null;
      interruptRecorder.onstop = null;
      interruptRecorder.stop();
    } catch {}
  }
  interruptRecorder = null;
  interruptRecording = false;
  interruptChunks = [];
  stopAllBrowserSpeechRecognizers();
  if (mediaRecorder && mediaRecorder.state === "recording") {
    suppressNextUtterance = true;
    mediaRecorder.stop();
  }
  processing = false;
  requestInFlight = false;
  voiceUxTurn = null;
  textUxTurn = null;
  pttRecording = false;
  listening = false;
  audioChunks = [];
  hasSpoken = false;
  lastVoiceTime = 0;
  waveState = "idle";
  setStatus("Ready", "idle");
  updateMuteInputButton();
}

function resumeAfterAssistantReplyPlayback() {
  browserAsrMainNetworkRetries = 0;
  processing = false;
  requestInFlight = false;
  if (workModeTypedTurnQueue.length > 0) scheduleWorkModeTypedQueueDrain();
  clearInterruptDetectionBubble();
  if (listeningMode === "ptt") {
    listening = false;
    pttRecording = false;
    waveState = "idle";
    setStatus("Ready", "idle");
    updateMuteInputButton();
    return;
  }
  waveState = "listening";
  if (listeningMode === "continuous") {
    listening = true;
    if (inputMuted) {
      showMutedStatusIfIdle();
      return;
    }
    /* Defer so Web Audio / <audio> teardown and NDJSON reader finish; avoids empty SR sessions that never transcribe. */
    window.setTimeout(() => {
      if (!listening || processing || inputMuted) return;
      startListening();
    }, 80);
  }
}

function resumeListeningAfterInterruptPlayback() {
  browserAsrMainNetworkRetries = 0;
  processing = false;
  requestInFlight = false;
  clearInterruptDetectionBubble();
  if (listeningMode === "ptt") {
    listening = false;
    pttRecording = false;
    waveState = "idle";
    setStatus("Ready", "idle");
    updateMuteInputButton();
    return;
  }
  waveState = "listening";
  listening = true;
  if (inputMuted) {
    showMutedStatusIfIdle();
    return;
  }
  window.setTimeout(() => {
    if (!listening || processing || inputMuted) return;
    startListening();
  }, 80);
}

/** Same wiring as MediaElementSource → analyser + destination: chunked TTS must feed the TTS analyser or BMO mouth / VERA wave stay flat. */
function connectBufferSourceToTtsGraph(src) {
  const m = appModePrefix();
  const t = ttsByMode[m];
  if (t?.analyser) {
    src.connect(t.analyser);
  }
  if (t?.gain) src.connect(t.gain);
  else src.connect(audioCtx.destination);
}

function wrapLastChunkForBmoMouth(onLastEnd) {
  if (!onLastEnd) return undefined;
  return () => {
    mainTtsPlaybackActive = false;
    if (document.body.classList.contains("bmo-open")) {
      stopBmoTtsMouthAnimation();
    }
    onLastEnd();
  };
}

/**
 * Schedule decoded buffers back-to-back on one AudioContext (minimal gaps vs chained <audio>).
 * Prefetches the next HTTP response while decoding/playing the current chunk.
 */
async function playTtsUrlSequenceGapless(
  baseUrl,
  relativeUrls,
  { onFirstStart, onLastEnd, sessionToken } = {}
) {
  if (!relativeUrls?.length) return;
  if (!audioCtx) {
    audioCtx = new AudioContext({ sampleRate: 16000 });
  }
  await audioCtx.resume();
  await ensureMainAudioTtsGraph();
  mainTtsPlaybackActive = true;
  getAudioEl()?.pause();
  let t = audioCtx.currentTime + 0.08;
  let firstDone = false;

  let nextPromise = fetch(`${baseUrl}${relativeUrls[0]}`).then((r) => {
    if (!r.ok) throw new Error(`TTS chunk 0 HTTP ${r.status}`);
    return r.arrayBuffer();
  });

  try {
  for (let i = 0; i < relativeUrls.length; i++) {
    if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
      mainTtsPlaybackActive = false;
      return;
    }
    const ab = await nextPromise;
    if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
      mainTtsPlaybackActive = false;
      return;
    }
    nextPromise =
      i + 1 < relativeUrls.length
        ? fetch(`${baseUrl}${relativeUrls[i + 1]}`).then((r) => {
            if (!r.ok) throw new Error(`TTS chunk ${i + 1} HTTP ${r.status}`);
            return r.arrayBuffer();
          })
        : null;

    const audBuf = await audioCtx.decodeAudioData(ab.slice(0));
    if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
      mainTtsPlaybackActive = false;
      return;
    }
    const src = audioCtx.createBufferSource();
    src.buffer = audBuf;
    connectBufferSourceToTtsGraph(src);
    const startAt = Math.max(t, audioCtx.currentTime + 0.02);
    src.start(startAt);
    /* BMO mouth before onFirstStart: onPlayStart applies news side panel (heavy innerHTML); blocking first would let TTS chunks finish before RAF starts — generic headlines path is slower than “breaking news”. */
    if (document.body.classList.contains("bmo-open")) {
      void startBmoTtsMouthAnimation();
    }
    if (!firstDone && onFirstStart) {
      onFirstStart();
      firstDone = true;
    }
    const isLast = i === relativeUrls.length - 1;
    registerMainTtsBufferSource(
      src,
      isLast && onLastEnd ? wrapLastChunkForBmoMouth(onLastEnd) : undefined
    );
    t = startAt + audBuf.duration;
  }
  } catch (e) {
    mainTtsPlaybackActive = false;
    throw e;
  }
}

/** Single <audio> for one file; Web Audio queue when multiple sentence chunks. */
async function playTtsFromApi(data, { onPlayStart, onPlayEnd } = {}) {
  if (appModePrefix() === "vera" && isVeraWorkModeOn() && isWorkModeMuteEnabled()) {
    logVeraSettings("tts_play_suppressed_workmode_mute", { mode: "playTtsFromApi" });
    mainTtsPlaybackActive = false;
    if (typeof onPlayStart === "function") onPlayStart();
    if (typeof onPlayEnd === "function") onPlayEnd();
    return;
  }
  const urls = resolveAudioUrls(data);
  if (!urls.length) return;

  if (urls.length > 1) {
    console.log(
      `[UX][TTS] ${urls.length} segments — one /text or /infer response; next: ${urls.length} GETs to /audio/...`,
      urls
    );
  }

  const sessionToken = mainTtsPlaybackToken;
  const runPlayStart = () => {
    if (onPlayStart) onPlayStart();
  };

  if (urls.length === 1) {
    const el = getAudioEl();
    if (!el) return;
    el.src = `${API_URL}${urls[0]}`;
    await ensureMainAudioTtsGraph();
    el.addEventListener(
      "play",
      () => {
        mainTtsPlaybackActive = true;
        if (document.body.classList.contains("bmo-open")) {
          void startBmoTtsMouthAnimation();
        }
        runPlayStart();
      },
      { once: true }
    );
    el.addEventListener(
      "ended",
      () => {
        mainTtsPlaybackActive = false;
        if (onPlayEnd) onPlayEnd();
      },
      { once: true }
    );
    await el.play();
    return;
  }

  await playTtsUrlSequenceGapless(API_URL, urls, {
    onFirstStart: runPlayStart,
    onLastEnd: onPlayEnd,
    sessionToken
  });
}

function createTtsUrlQueue() {
  const q = [];
  const waiters = [];
  let ended = false;
  return {
    push(url) {
      q.push(url);
      const w = waiters.shift();
      if (w) w();
    },
    end() {
      ended = true;
      waiters.splice(0).forEach((w) => w());
    },
    async next() {
      for (;;) {
        if (q.length) return q.shift();
        if (ended) return null;
        await new Promise((r) => waiters.push(r));
      }
    }
  };
}

/** Gapless Web Audio playback when URLs arrive incrementally (streaming NDJSON chunks). */
async function playTtsUrlSequenceIncremental(
  baseUrl,
  nextRelFn,
  { onBeforeFirstPlay, onFirstStart, onLastEnd, sessionToken } = {}
) {
  if (!audioCtx) {
    audioCtx = new AudioContext({ sampleRate: 16000 });
  }
  await audioCtx.resume();
  await ensureMainAudioTtsGraph();
  let t = audioCtx.currentTime + 0.08;
  let firstDone = false;

  let curRel = await nextRelFn();
  if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
    mainTtsPlaybackActive = false;
    return;
  }
  /* NDJSON can call queue.end() before any chunk URL (e.g. done-before-chunk or empty TTS). Without this,
     onPlayEnd / resumeAfterAssistantReplyPlayback never runs → processing stays true and listening never renews. */
  if (!curRel) {
    const endFn = onLastEnd ? wrapLastChunkForBmoMouth(onLastEnd) : null;
    if (endFn) endFn();
    else mainTtsPlaybackActive = false;
    return;
  }
  mainTtsPlaybackActive = true;
  getAudioEl()?.pause();
  let nextPromise = fetch(`${baseUrl}${curRel}`).then((r) => {
    if (!r.ok) throw new Error(`TTS HTTP ${r.status}`);
    return r.arrayBuffer();
  });

  try {
  for (;;) {
    if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
      mainTtsPlaybackActive = false;
      return;
    }
    const ab = await nextPromise;
    if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
      mainTtsPlaybackActive = false;
      return;
    }
    const nextRel = await nextRelFn();
    if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
      mainTtsPlaybackActive = false;
      return;
    }
    nextPromise = nextRel
      ? fetch(`${baseUrl}${nextRel}`).then((r) => {
          if (!r.ok) throw new Error(`TTS HTTP ${r.status}`);
          return r.arrayBuffer();
        })
      : null;

    const audBuf = await audioCtx.decodeAudioData(ab.slice(0));
    if (sessionToken !== undefined && mainTtsPlaybackToken !== sessionToken) {
      mainTtsPlaybackActive = false;
      return;
    }
    if (!firstDone && onBeforeFirstPlay) {
      onBeforeFirstPlay();
    }
    const src = audioCtx.createBufferSource();
    src.buffer = audBuf;
    connectBufferSourceToTtsGraph(src);
    const startAt = Math.max(t, audioCtx.currentTime + 0.02);
    src.start(startAt);
    /* Same order as gapless: mouth before onPlayStart so heavy news panel does not block first tick. */
    if (document.body.classList.contains("bmo-open")) {
      void startBmoTtsMouthAnimation();
    }
    if (!firstDone && onFirstStart) {
      onFirstStart();
      firstDone = true;
    }
    const isLast = !nextRel;
    registerMainTtsBufferSource(
      src,
      isLast && onLastEnd ? wrapLastChunkForBmoMouth(onLastEnd) : undefined
    );
    t = startAt + audBuf.duration;
    if (!nextRel) break;
  }
  } catch (e) {
    mainTtsPlaybackActive = false;
    throw e;
  }
}

/**
 * Consume application/x-ndjson: asr (optional) → meta → chunk → … → done. Prefetches the next URL while decoding/playing.
 * Each parsed line batch must be handled in stream order: meta before chunks, or the user transcript bubble
 * can appear after the assistant (same bug for main infer and interrupt NDJSON).
 * First-sentence assistant text is applied in onBeforeFirstPlay (after decode, before src.start) so it aligns with audio.
 */
async function runNdjsonTtsPlayback(res, { onMeta, onDone, onPlayStart, onPlayEnd, onReplyProgress }) {
  const reader = res.body.getReader();
  activeNdjsonBodyReader = reader;
  const sessionToken = mainTtsPlaybackToken;
  const decoder = new TextDecoder();
  let buf = "";
  const queue = createTtsUrlQueue();
  let loggedFirstChunk = false;
  /** User bubble from transcript: once from early `asr` line or from `meta` (older servers). */
  let userTranscriptBubbleSeen = false;
  function wrapOnMeta(meta) {
    if (!onMeta || !meta) return;
    const m = { ...meta };
    if (m.transcript) {
      if (userTranscriptBubbleSeen) {
        delete m.transcript;
      } else {
        userTranscriptBubbleSeen = true;
      }
    }
    onMeta(m);
  }
  /** First-sentence text is deferred until first audio buffer is decoded (sync with playback start). */
  let pendingFirstReplySoFar = null;
  let deferFirstReply = true;
  /** Latest reply_so_far already applied via onReplyProgress (avoids onBeforeFirstPlay overwriting with shorter pending). */
  let lastEmittedReplySoFar = null;

  async function readAll() {
    try {
      while (true) {
        if (mainTtsPlaybackToken !== sessionToken) {
          queue.end();
          return;
        }
        let readResult;
        try {
          readResult = await reader.read();
        } catch {
          queue.end();
          return;
        }
        const { value, done: rdone } = readResult;
        if (rdone) break;
        buf += decoder.decode(value, { stream: true });
        const lines = buf.split("\n");
        buf = lines.pop() || "";
        const objs = [];
        for (const line of lines) {
          if (!line.trim()) continue;
          try {
            objs.push(JSON.parse(line));
          } catch (e) {
            console.warn("[TTS][NDJSON] skip line", e);
          }
        }
        for (const obj of objs) {
          if (obj.type === "asr" && obj.transcript != null) {
            wrapOnMeta({ transcript: String(obj.transcript) });
            logVoicePipe("NDJSON asr line (user transcript early)");
          } else if (obj.type === "meta") {
            wrapOnMeta(obj);
            logVoicePipe("NDJSON meta line (UI can attach transcript)");
          } else if (obj.type === "chunk" && obj.url) {
            if (mainTtsPlaybackToken !== sessionToken) {
              queue.end();
              return;
            }
            if (!loggedFirstChunk) {
              loggedFirstChunk = true;
              logVoicePipe("NDJSON first chunk URL queued (GET /audio/... next)");
            }
            queue.push(obj.url);
            if (obj.reply_so_far != null && onReplyProgress) {
              if (deferFirstReply) {
                pendingFirstReplySoFar = String(obj.reply_so_far);
                deferFirstReply = false;
              } else {
                onReplyProgress(obj.reply_so_far);
                lastEmittedReplySoFar = String(obj.reply_so_far);
              }
            }
          } else if (obj.type === "done") {
            if (onDone) onDone(obj);
            queue.end();
          }
        }
      }
    } finally {
      queue.end();
      if (activeNdjsonBodyReader === reader) activeNdjsonBodyReader = null;
    }
  }

  const readTask = readAll();
  try {
    await Promise.all([
      playTtsUrlSequenceIncremental(API_URL, () => queue.next(), {
        onBeforeFirstPlay: () => {
          if (pendingFirstReplySoFar != null && onReplyProgress) {
            const pending = pendingFirstReplySoFar;
            pendingFirstReplySoFar = null;
            const alreadyAhead =
              lastEmittedReplySoFar != null &&
              lastEmittedReplySoFar.length >= pending.length;
            if (!alreadyAhead) {
              onReplyProgress(pending);
              lastEmittedReplySoFar = pending;
            }
          }
        },
        onFirstStart: onPlayStart,
        onLastEnd: onPlayEnd,
        sessionToken
      }),
      readTask
    ]);
  } finally {
    if (activeNdjsonBodyReader === reader) activeNdjsonBodyReader = null;
  }
}

async function initMic() {
  if (micStream) return;

  const audioConstraints = isNarrowViewport()
    ? {
        echoCancellation: true,
        noiseSuppression: true,
        autoGainControl: true,
      }
    : {
        echoCancellation: false,
        noiseSuppression: false,
        autoGainControl: false,
      };

  micStream = await navigator.mediaDevices.getUserMedia({ audio: audioConstraints });

  if (!audioCtx) {
    audioCtx = new AudioContext({ sampleRate: 16000 });
  }
  await audioCtx.resume();
  resizeWaveCanvas();

  analyser = audioCtx.createAnalyser();
  analyser.fftSize = 2048;

  audioCtx.createMediaStreamSource(micStream).connect(analyser);

  await ensureMainAudioTtsGraph();

  detectInterrupt();
  startWaveAnimation();
  updateMuteInputButton();
}
/* =========================
   WAVE ANIMATION
   - Frequency-band bars (FFT): bass → treble, amplitude per band
   - Ripple effect: concentric circles that pulse outward with amplitude
========================= */

const BARS = 48;  // frequency bands (bass on sides, treble toward center for symmetry)
const RIPPLE_EXPAND_SPEED = 2.2;
const RIPPLE_FADE_SPEED = 0.018;
const RIPPLE_SPAWN_THRESHOLD = 0.12;  // min avg magnitude to spawn ripple

function freqDataToBands(analyserRef, freqBuf, barValues) {
  if (!analyserRef || !freqBuf) return;
  analyserRef.getByteFrequencyData(freqBuf);
  const binCount = freqBuf.length;
  // Log-like band mapping: more resolution in bass/low-mids (where voice lives)
  for (let i = 0; i < BARS; i++) {
    const fracStart = Math.pow(i / BARS, 1.4);
    const fracEnd = Math.pow((i + 1) / BARS, 1.4);
    const binStart = Math.floor(fracStart * binCount);
    const binEnd = Math.min(Math.ceil(fracEnd * binCount), binCount);
    let sum = 0;
    let n = 0;
    for (let b = binStart; b < binEnd; b++) {
      sum += freqBuf[b];
      n++;
    }
    barValues[i] = n > 0 ? sum / n / 255 : 0;
  }
}

function startWaveAnimation() {
  if (waveformRaf) return;

  function draw() {
    waveformRaf = requestAnimationFrame(draw);

    const canvas = getWaveCanvas();
    const waveCtx = getWaveCtx();
    if (!canvas || !waveCtx) return;

    const dpr = window.devicePixelRatio || 1;
    const width = canvas.width / dpr;
    const height = canvas.height / dpr;
    const centerX = width / 2;
    const centerY = height / 2;

    waveCtx.clearRect(0, 0, width, height);

    const bmoOpen = document.body.classList.contains("bmo-open");
    /* BMO: waveform only while user is speaking (listening); TTS uses SVG mouth */
    if (bmoOpen && waveState === "speaking") {
      return;
    }

    const ttsA = getTtsAnalyser();
    let activeAnalyser = null;
    if (waveState === "listening" && analyser) activeAnalyser = analyser;
    if (waveState === "speaking" && ttsA) activeAnalyser = ttsA;

    if (!frequencyData || !activeAnalyser || frequencyData.length !== activeAnalyser.frequencyBinCount) {
      if (activeAnalyser) {
        frequencyData = new Uint8Array(activeAnalyser.frequencyBinCount);
        smoothedBars = new Float32Array(BARS);
      }
    }

    const targetEnergy = waveState === "speaking" ? 0.9 : waveState === "listening" ? 0.8 : 0;
    waveEnergy += (targetEnergy - waveEnergy) * 0.06;

    const barValues = new Float32Array(BARS);
    if (activeAnalyser && frequencyData) {
      freqDataToBands(activeAnalyser, frequencyData, barValues);
    }

    const barSpacing = width / BARS;
    const barWidth = barSpacing * 0.4;
    let avgMagnitude = 0;

    for (let i = 0; i < BARS; i++) {
      const v = barValues[i];
      avgMagnitude += v;
      const smooth = 0.25;
      if (smoothedBars) smoothedBars[i] = smoothedBars[i] * (1 - smooth) + v * smooth;
    }
    avgMagnitude /= BARS;

    const now = performance.now();
    if (waveEnergy > 0.3 && avgMagnitude > RIPPLE_SPAWN_THRESHOLD && now - lastRippleTime > RIPPLE_SPAWN_INTERVAL_MS) {
      rippleRings.push({ radius: 0, opacity: 0.5 + avgMagnitude * 0.4 });
      lastRippleTime = now;
    }

    for (let r = rippleRings.length - 1; r >= 0; r--) {
      const ring = rippleRings[r];
      ring.radius += RIPPLE_EXPAND_SPEED;
      ring.opacity -= RIPPLE_FADE_SPEED;
      if (ring.opacity <= 0) {
        rippleRings.splice(r, 1);
        continue;
      }
      const rippleAlpha = bmoOpen ? ring.opacity * 0.42 : ring.opacity * 0.35;
      const rr = bmoOpen ? 8 : 255;
      const rg = bmoOpen ? 72 : 255;
      const rb = bmoOpen ? 46 : 255;
      waveCtx.strokeStyle = `rgba(${rr},${rg},${rb},${rippleAlpha})`;
      waveCtx.lineWidth = 1.5;
      waveCtx.beginPath();
      waveCtx.arc(centerX, centerY, ring.radius, 0, Math.PI * 2);
      waveCtx.stroke();
    }

    const boost = waveState === "speaking" ? 2.8 : waveState === "listening" ? 2.8 : 0;
    const minimumBarScale = waveState === "listening" ? 0.05 : 0.03;
    const mid = BARS / 2;
    if (bmoOpen) {
      waveCtx.fillStyle = "rgba(10, 68, 42, 0.98)";
      /* Lighter shadow than VERA: mint bar + heavy blur reads as muddy / soft. */
      waveCtx.shadowBlur = 3;
      waveCtx.shadowColor = "rgba(4, 42, 26, 0.35)";
    } else {
      waveCtx.fillStyle = "rgba(255,255,255,0.95)";
      waveCtx.shadowBlur = 14;
      waveCtx.shadowColor = "rgba(255,255,255,0.7)";
    }

    for (let i = 0; i < BARS; i++) {
      const raw = (smoothedBars && waveEnergy > 0) ? smoothedBars[i] : barValues[i];
      const distance = Math.abs(i - mid) / mid;
      const envelope = Math.pow(1 - distance, 2.0);
      const barHeight =
        Math.max(minimumBarScale, raw) * height * boost * envelope * waveEnergy;

      const x = i * barSpacing + (barSpacing - barWidth) / 2;
      waveCtx.beginPath();
      waveCtx.roundRect(x, centerY - barHeight, barWidth, barHeight * 2, barWidth / 2);
      waveCtx.fill();
    }
  }

  draw();
}

/* =========================
   BMO — TTS drives SVG mouth (same shaping as intro in index.html)
========================= */

/**
 * BMO TTS mouth: idle (stroke) / surprised (O) / happy (open).
 *
 * What drives it:
 * - **Instant level** ≈ waveform RMS + a little **FFT peak** (tallest bin in the voice band).
 *   We deliberately use almost no **band average**: that stays high for all vowels and was
 *   keeping you stuck on "happy".
 * - **Happy** when **loudness spikes above a slow baseline** (syllable edges), not when level
 *   sits flat high — flat TTS used to keep `instant ≈ peakHold` forever → stuck on happy.
 * - **Surprised** during steady voiced segments (baseline catches up, “excess” drops).
 * - **Idle** when instant + speech body are low (tiny pauses).
 */
const BMO_TTS_MOUTH_ENERGY_GAIN = 4.35;
/** Voice-ish bins for ~48 kHz / 2048 FFT: bin ~4 → ~94 Hz, cap ~3 kHz. */
const BMO_TTS_FREQ_BIN_START = 4;
const BMO_TTS_FREQ_BIN_END = 128;
/** Slow baseline under instant; higher = baseline lags more → more happy vs mostly surprised. */
const BMO_TTS_BASELINE_EMA = 0.946;
/** Decay on the spike memory of (instant − baseline); lower = snappier surprised between hits. */
const BMO_TTS_EXCESS_PEAK_DECAY = 0.73;
/** Excess must be this close to its decaying peak to count as a hit (higher = shorter happy). */
const BMO_TTS_EXCESS_NEAR_PEAK_FRAC = 0.75;
/** Minimum “bump” above baseline to open happy (noise gate on spikes). */
const BMO_TTS_MIN_EXCESS_HAPPY = 0.022;
/** Slow envelope mix: speech present vs gap (surprised vs idle). */
const BMO_TTS_SPEECH_BODY_EMA = 0.86;

const bmoPageForTts = document.getElementById("bmo-page");

let bmoTtsMouthRaf = null;
let bmoTtsMouthTime = null;
let bmoTtsMouthFreq = null;
let bmoTtsBaseline = 0;
let bmoTtsExcessPeak = 0;
let bmoTtsSpeechBody = 0;
let bmoTtsEmotion = "idle";

function bmoComputeTtsInstant01(ttsA, timeBuf, freqBuf) {
  ttsA.getByteTimeDomainData(timeBuf);
  let rms = 0;
  for (let i = 0; i < timeBuf.length; i++) {
    const v = (timeBuf[i] - 128) / 128;
    rms += v * v;
  }
  rms = Math.sqrt(rms / timeBuf.length);
  const rms01 = Math.min(1, rms * BMO_TTS_MOUTH_ENERGY_GAIN);

  ttsA.getByteFrequencyData(freqBuf);
  const i0 = Math.min(BMO_TTS_FREQ_BIN_START, freqBuf.length);
  const i1 = Math.min(BMO_TTS_FREQ_BIN_END, freqBuf.length);
  let peak = 0;
  for (let i = i0; i < i1; i++) {
    const b = freqBuf[i];
    if (b > peak) peak = b;
  }
  const bandPeak = peak / 255;

  /* RMS + FFT peak: tiny bit more peak helps happy fire on spectral hits without flattening prosody. */
  return Math.min(1, rms01 * 0.9 + bandPeak * 0.3);
}

/**
 * nearPeak: true when loudness is spiking above the slow baseline (not sustained flat).
 * speechBody: slow level for "still talking" vs tiny gaps → surprised vs idle.
 */
function bmoStepTtsEmotion(nearPeak, speechBody, instant, prev) {
  const idleCut = 0.052;
  const idleCutHyst = 0.062;

  if (prev === "happy") {
    if (speechBody < idleCut && instant < 0.06) return "idle";
    if (!nearPeak) return "surprised";
    return "happy";
  }
  if (prev === "surprised") {
    if (speechBody < idleCut && instant < 0.055) return "idle";
    if (nearPeak) return "happy";
    return "surprised";
  }
  if (speechBody > idleCutHyst || instant > 0.085) return "surprised";
  if (nearPeak) return "happy";
  return "idle";
}

function stopBmoTtsMouthAnimation() {
  if (bmoTtsMouthRaf) {
    cancelAnimationFrame(bmoTtsMouthRaf);
    bmoTtsMouthRaf = null;
  }
  bmoPageForTts?.classList.remove("bmo-tts-mouth");
  document.getElementById("bmo-smile-svg")?.removeAttribute("data-bmo-tts-emotion");
  bmoTtsBaseline = 0;
  bmoTtsExcessPeak = 0;
  bmoTtsSpeechBody = 0;
  bmoTtsEmotion = "idle";
}

function tickBmoTtsMouth() {
  if (!bmoPageForTts?.classList.contains("bmo-tts-mouth")) {
    stopBmoTtsMouthAnimation();
    return;
  }
  if (!document.body.classList.contains("bmo-open")) {
    stopBmoTtsMouthAnimation();
    return;
  }
  const smileSvg = document.getElementById("bmo-smile-svg");
  const ttsA = ttsByMode.bmo.analyser;
  const bmoOut = document.getElementById("bmo-audio");
  if (!smileSvg || !ttsA) {
    stopBmoTtsMouthAnimation();
    return;
  }
  const webAudioTtsPlaying = activeMainTtsBufferSources.length > 0;
  if (
    !bmoOut ||
    (!webAudioTtsPlaying &&
      !mainTtsPlaybackActive &&
      (bmoOut.paused || bmoOut.ended))
  ) {
    stopBmoTtsMouthAnimation();
    return;
  }
  if (!bmoTtsMouthTime || bmoTtsMouthTime.length !== ttsA.fftSize) {
    bmoTtsMouthTime = new Uint8Array(ttsA.fftSize);
  }
  if (!bmoTtsMouthFreq || bmoTtsMouthFreq.length !== ttsA.frequencyBinCount) {
    bmoTtsMouthFreq = new Uint8Array(ttsA.frequencyBinCount);
  }

  const instant = bmoComputeTtsInstant01(ttsA, bmoTtsMouthTime, bmoTtsMouthFreq);
  bmoTtsBaseline =
    bmoTtsBaseline * BMO_TTS_BASELINE_EMA + instant * (1 - BMO_TTS_BASELINE_EMA);
  const excess = Math.max(0, instant - bmoTtsBaseline);
  bmoTtsExcessPeak = Math.max(excess, bmoTtsExcessPeak * BMO_TTS_EXCESS_PEAK_DECAY);
  const nearPeak =
    excess >= bmoTtsExcessPeak * BMO_TTS_EXCESS_NEAR_PEAK_FRAC &&
    excess >= BMO_TTS_MIN_EXCESS_HAPPY;
  bmoTtsSpeechBody =
    bmoTtsSpeechBody * BMO_TTS_SPEECH_BODY_EMA + instant * (1 - BMO_TTS_SPEECH_BODY_EMA);
  bmoTtsEmotion = bmoStepTtsEmotion(nearPeak, bmoTtsSpeechBody, instant, bmoTtsEmotion);
  smileSvg.setAttribute("data-bmo-tts-emotion", bmoTtsEmotion);

  bmoTtsMouthRaf = requestAnimationFrame(tickBmoTtsMouth);
}

async function startBmoTtsMouthAnimation() {
  if (!document.body.classList.contains("bmo-open") || !bmoPageForTts) return;
  try {
    await ensureMainAudioTtsGraph();
  } catch (e) {
    console.warn("BMO TTS graph", e);
    return;
  }
  if (!ttsByMode.bmo.analyser) return;
  bmoPageForTts.classList.add("bmo-tts-mouth");
  document.getElementById("bmo-smile-svg")?.setAttribute("data-bmo-tts-emotion", "idle");
  bmoTtsBaseline = 0;
  bmoTtsExcessPeak = 0;
  bmoTtsSpeechBody = 0;
  bmoTtsEmotion = "idle";
  if (bmoTtsMouthRaf) return;
  bmoTtsMouthRaf = requestAnimationFrame(tickBmoTtsMouth);
}

document.getElementById("bmo-audio")?.addEventListener("playing", () => {
  void startBmoTtsMouthAnimation();
});
document.getElementById("bmo-audio")?.addEventListener("pause", () => {
  /* Chunked TTS keeps <audio> paused while BufferSources play; do not kill the mouth on that pause. */
  if (activeMainTtsBufferSources.length > 0 || mainTtsPlaybackActive) return;
  stopBmoTtsMouthAnimation();
});
document.getElementById("bmo-audio")?.addEventListener("ended", () => {
  stopBmoTtsMouthAnimation();
});

/* =========================
   SPEECH DETECTION
========================= */

function detectSpeech() {
  if (!mediaRecorder || mediaRecorder.state !== "recording") return;

  const buf = new Float32Array(analyser.fftSize);
  analyser.getFloatTimeDomainData(buf);

  let sum = 0;
  for (let i = 0; i < buf.length; i++) sum += buf[i] * buf[i];
  const rms = Math.sqrt(sum / buf.length);

  const now = performance.now();

  if (listeningFrameIsSpeechLike(buf, rms)) {
    hasSpoken = true;
    lastVoiceTime = now;
  }

  if (
    hasSpoken &&
    now - lastVoiceTime > SILENCE_MS + TRAILING_MS &&
    (getAudioEl()?.paused ?? true) // 🔑 only stop when not speaking
  ) {
    beginVoiceUxTurn();
    mediaRecorder.stop();
    return;
  }

  rafId = requestAnimationFrame(detectSpeech);
}

function clearSpeechWaitTimerAndDetectRaf() {
  if (speechWaitTimeoutId != null) {
    clearTimeout(speechWaitTimeoutId);
    speechWaitTimeoutId = null;
  }
  if (rafId != null) {
    cancelAnimationFrame(rafId);
    rafId = null;
  }
}

/**
 * End continuous capture without uploading (e.g. switching to PTT). Clears the no-speech
 * timer so it cannot fire on the next `mediaRecorder` instance.
 */
function stopActiveMicCaptureSilently() {
  clearSpeechWaitTimerAndDetectRaf();
  if (mediaRecorder && mediaRecorder.state === "recording") {
    suppressNextUtterance = true;
    mediaRecorder.stop();
  }
  stopAllBrowserSpeechRecognizers();
}

/** Stop Web Speech + timers; does not remove the live partial bubble (used before /infer so we can promote the same node). */
function abortBrowserSpeechRecognizers() {
  if (interruptDetectNoResultWatchdogTimer != null) {
    clearTimeout(interruptDetectNoResultWatchdogTimer);
    interruptDetectNoResultWatchdogTimer = null;
  }
  if (browserAsrMainEndRecoveryTimer != null) {
    clearTimeout(browserAsrMainEndRecoveryTimer);
    browserAsrMainEndRecoveryTimer = null;
  }
  if (browserAsrStuckDebugEnabled()) {
    logBrowserAsrStuckEvent("abortBrowserSpeechRecognizers");
  }
  stopBrowserAsrStuckWatchdog();
  if (mainBrowserSilenceTimer != null) {
    clearTimeout(mainBrowserSilenceTimer);
    mainBrowserSilenceTimer = null;
  }
  [mainBrowserRecognition, interruptDetectRecognition, postInterruptRecognition].forEach(
    (r) => {
      if (!r) return;
      try {
        r.onresult = null;
        r.onerror = null;
        r.onend = null;
        r.abort();
      } catch {
        try {
          r.stop();
        } catch {}
      }
    }
  );
  mainBrowserRecognition = null;
  interruptDetectRecognition = null;
  postInterruptRecognition = null;
  interruptBrowserDetectActive = false;
  interruptPartialAccumMs = 0;
  interruptPartialLastChangeAt = 0;
  interruptPartialLastText = "";
  interruptBargeInLatched = false;
  mainBrowserFinalTranscript = "";
  mainBrowserFinalizeKind = "main";
  mainBrowserLastInterim = "";
}

function stopAllBrowserSpeechRecognizers() {
  abortBrowserSpeechRecognizers();
  try {
    if (mainBrowserLiveBubble?.isConnected) {
      mainBrowserLiveBubble.remove();
    }
  } catch (_) {}
  mainBrowserLiveBubble = null;
  clearInterruptDetectionBubble();
}

/**
 * Two separate `SpeechRecognition` instances: `mainBrowserRecognition` (user turn) and
 * `interruptDetectRecognition` (barge-in while assistant speaks). Chrome only reliably allows
 * one active session at a time — they are sequenced (main aborted before /infer; interrupt starts
 * at TTS `onPlayStart`; main restarts after playback ends).
 *
 * Leaked interrupt-detect handles block main `onend` recovery; we abort stale ones only when the
 * assistant is not still in a reply (`waveState !== "speaking"` and `!isAssistantTtsPlaying()`).
 * Do not tear down between streamed TTS chunks: `waveState` stays `"speaking"` even when buffers
 * are momentarily empty.
 */
function tearDownLeakedInterruptDetectSpeechRecognitionIfIdle() {
  if (!interruptDetectRecognition || interruptBargeInLatched) return;
  if (waveState === "speaking") return;
  if (isAssistantTtsPlaying()) return;
  try {
    interruptDetectRecognition.abort();
  } catch {}
  interruptDetectRecognition = null;
  interruptBrowserDetectActive = false;
  clearInterruptDetectionBubble();
}

/** After main SR `onend` or tab visible: restart main capture if we still expect desktop browser ASR. */
function maybeResumeMainBrowserSpeechRecognition(reason) {
  if (!listening || processing || inputMuted) return;
  if (waveState === "speaking") return;
  if (isAssistantTtsPlaying()) return;
  if (listeningMode !== "continuous" || !browserAsrPreferred()) return;
  tearDownLeakedInterruptDetectSpeechRecognitionIfIdle();
  if (mainBrowserRecognition || interruptDetectRecognition || postInterruptRecognition) return;
  console.info(`[BrowserASR] resume main SpeechRecognition (${reason})`);
  startListening();
}

function scheduleMainBrowserEndOfUtterance() {
  if (mainBrowserSilenceTimer != null) {
    clearTimeout(mainBrowserSilenceTimer);
    mainBrowserSilenceTimer = null;
  }
  const snap = (mainBrowserFinalTranscript + "").trim();
  mainBrowserSilenceTimer = setTimeout(() => {
    mainBrowserSilenceTimer = null;
    const cur = (mainBrowserFinalTranscript + "").trim();
    if (cur !== snap || cur.length === 0) {
      if (browserAsrStuckDebugEnabled()) {
        logBrowserAsrStuckEvent("silence_timer_fired_no_finalize", {
          reason: cur.length === 0 ? "empty_final" : "final_transcript_changed_since_schedule",
          snapAtSchedule: snap.slice(0, 80),
          curFinalNow: cur.slice(0, 80),
          interimNow: (mainBrowserLastInterim || "").slice(0, 80),
          finalizeKind: mainBrowserFinalizeKind,
        });
      }
      return;
    }
    const finalizeNow = () => {
      const cur2 = (mainBrowserFinalTranscript + "").trim();
      if (cur2.length === 0) return;
      logPartialAsrUtteranceDone(cur2, {
        reason: "silence-timer",
        mode: mainBrowserFinalizeKind === "interrupt" ? "interrupt" : "main"
      });
      if (mainBrowserFinalizeKind === "interrupt") {
        void finalizeInterruptBrowserTranscript(cur2);
      } else {
        void finalizeMainBrowserTranscript(cur2);
      }
    };
    finalizeNow();
  }, browserAsrMainSilenceMs);
  logVeraSettings("schedule_asr_silence_timer", {
    ms: browserAsrMainSilenceMs,
    asr_mode: getVeraAsrMode()
  });
}

function updateMainBrowserLiveBubble(fullText, interim) {
  const convo = uiEl("conversation");
  if (!convo) return;
  const line = (fullText + interim).trim();
  const hasFinal = String(fullText || "").trim().length > 0;
  if (!hasFinal && line.length < mainAsrPartialMinChars) return;
  if (!line) return;
  if (!mainBrowserLiveBubble || !mainBrowserLiveBubble.isConnected) {
    mainBrowserLiveBubble = addBubble(line, "user", { path: "main-browser-partial" });
  } else {
    mainBrowserLiveBubble.textContent = line;
  }
  convo.scrollTop = convo.scrollHeight;
}

function removeMainBrowserLiveBubble() {
  if (mainBrowserLiveBubble?.isConnected) {
    mainBrowserLiveBubble.remove();
  }
  mainBrowserLiveBubble = null;
}

async function finalizeMainBrowserTranscript(text) {
  const trimmed = (text || "").trim();
  if (!trimmed) {
    stopAllBrowserSpeechRecognizers();
    processing = false;
    voiceUxTurn = null;
    if (listeningMode === "continuous" && listening && !inputMuted) {
      startListening();
    }
    return;
  }
  if (await maybeHandleWorkChecklistPlanShortcut(trimmed)) {
    return;
  }

  /* Set before stopAll so a sync SpeechRecognition "onend" cannot restart ASR while we're entering infer. */
  processing = true;
  requestInFlight = true;
  beginVoiceUxTurn();
  waveState = "idle";
  setStatus("Thinking", "thinking");

  /* Keep partial bubble in DOM; commitServerUserTranscriptBubble updates the same node when /infer returns. */
  abortBrowserSpeechRecognizers();

  const formData = new FormData();
  formData.append("transcript", trimmed);
  formData.append("use_browser_asr", "1");
  formData.append("session_id", getSessionId());
  formData.append("client", appModePrefix());
  formData.append("context_snapshot", JSON.stringify(buildClientContextSnapshot()));
  if (listeningMode === "ptt") {
    formData.append("mode", "ptt");
  }
  formData.append("stream_tts", shouldStreamTts() ? "1" : "0");

  logVoiceTranscript("final", trimmed, { path: "main-browser-asr" });
  logFinalTranscriptSentToLlm("main-browser-asr", trimmed);
  attachPipelineAbortSignal();
  const pipelineSig = activePipelineAbort.signal;
  await maybePrepareWorkModeReasoning(formData, trimmed, pipelineSig);
  await runInferMainPipeline(formData, { signal: pipelineSig });
}

function startMainBrowserRecognitionContinuous() {
  const SR = window.SpeechRecognition || window.webkitSpeechRecognition;
  if (!SR) return;

  stopAllBrowserSpeechRecognizers();
  mainBrowserFinalizeKind = "main";

  mainBrowserFinalTranscript = "";
  let interimBuf = "";

  mainBrowserRecognition = new SR();
  mainBrowserRecognition.continuous = true;
  mainBrowserRecognition.interimResults = true;
  mainBrowserRecognition.lang = getSpeechRecognitionLang();

  mainBrowserRecognition.onresult = (event) => {
    browserAsrMainNetworkRetries = 0;
    markBrowserAsrResult("main");
    interimBuf = "";
    for (let i = event.resultIndex; i < event.results.length; i++) {
      const r = event.results[i];
      if (r.isFinal) {
        const piece = r[0].transcript;
        mainBrowserFinalTranscript += piece;
        logPartialAsrSegmentFinal(piece.trim(), { mode: "main" });
      } else {
        interimBuf += r[0].transcript;
      }
    }
    mainBrowserLastInterim = interimBuf;
    hasSpoken = mainBrowserFinalTranscript.trim().length > 0 || interimBuf.trim().length > 0;
    if (hasSpoken && speechWaitTimeoutId != null) {
      clearTimeout(speechWaitTimeoutId);
      speechWaitTimeoutId = null;
    }
    updateMainBrowserLiveBubble(mainBrowserFinalTranscript, interimBuf);
    scheduleMainBrowserEndOfUtterance();
  };

  mainBrowserRecognition.onerror = (ev) => {
    if (browserAsrStuckDebugEnabled()) {
      logBrowserAsrStuckEvent("main onerror", { error: ev.error, message: ev.message });
    }
    if (ev.error === "aborted" || ev.error === "no-speech") return;
    if (ev.error === "network") {
      if (browserAsrMainNetworkRetries < BROWSER_ASR_MAIN_NETWORK_RETRY_MAX) {
        browserAsrMainNetworkRetries++;
        console.warn("[BrowserASR] network — retrying SpeechRecognition", browserAsrMainNetworkRetries);
        window.setTimeout(() => {
          if (!listening || processing || inputMuted) return;
          if (listeningMode !== "continuous" || !browserAsrPreferred()) return;
          startListening();
        }, 750);
        return;
      }
    }
    console.warn("[BrowserASR]", ev.error);
    if (isFatalBrowserSpeechError(ev.error)) {
      disableBrowserAsrForSession(ev.error);
      stopAllBrowserSpeechRecognizers();
      processing = false;
      voiceUxTurn = null;
      if (listeningMode === "continuous" && listening && !inputMuted) {
        setStatus("Use http://localhost or HTTPS for live captions — using mic recording", "recording");
        startListening();
      }
    }
  };

  mainBrowserRecognition.onend = () => {
    logBrowserAsrStuckEvent(
      "main onend (session ended — if unexpected while listening, partial ASR may look stuck)",
      { note: "scheduling guarded recovery if still in continuous listen mode" }
    );
    mainBrowserRecognition = null;
    /* Intentionally no synchronous restart: abort/stop during infer must not recreate SR. After natural end
       (common after long TTS gaps), renew listening once if we still expect continuous browser ASR. */
    if (browserAsrMainEndRecoveryTimer != null) {
      clearTimeout(browserAsrMainEndRecoveryTimer);
      browserAsrMainEndRecoveryTimer = null;
    }
    browserAsrMainEndRecoveryTimer = window.setTimeout(() => {
      browserAsrMainEndRecoveryTimer = null;
      maybeResumeMainBrowserSpeechRecognition("main-onend");
    }, 420);
  };

  try {
    mainBrowserRecognition.start();
    beginBrowserAsrStuckSession("main");
  } catch (e) {
    console.warn("[BrowserASR] start failed", e);
    window.setTimeout(() => {
      if (!listening || processing || inputMuted) return;
      if (listeningMode !== "continuous" || !browserAsrPreferred()) return;
      startListening();
    }, 150);
  }

  if (MAX_WAIT_FOR_BROWSER_ASR_INITIAL_MS > 0) {
    speechWaitTimeoutId = setTimeout(() => {
      speechWaitTimeoutId = null;
      if (!hasSpoken) {
        stopAllBrowserSpeechRecognizers();
        processing = false;
        voiceUxTurn = null;
      }
    }, MAX_WAIT_FOR_BROWSER_ASR_INITIAL_MS);
  }
}

function startInterruptBrowserPartialDetection() {
  const SR = window.SpeechRecognition || window.webkitSpeechRecognition;
  if (!SR) return;

  if (interruptDetectNoResultWatchdogTimer != null) {
    clearTimeout(interruptDetectNoResultWatchdogTimer);
    interruptDetectNoResultWatchdogTimer = null;
  }

  clearInterruptDetectionBubble();
  interruptBargeInLatched = false;

  try {
    if (interruptDetectRecognition) {
      interruptDetectRecognition.abort();
    }
  } catch {}

  interruptDetectRecognition = new SR();
  interruptDetectRecognition.continuous = true;
  interruptDetectRecognition.interimResults = true;
  interruptDetectRecognition.lang = getSpeechRecognitionLang();

  let lastCombined = "";
  interruptPartialAccumMs = 0;
  interruptPartialLastChangeAt = 0;
  interruptPartialLastText = "";
  interruptPartialRafTime = performance.now();
  interruptBrowserDetectActive = true;

  let hadAnyResult = false;

  interruptDetectRecognition.onresult = (event) => {
    if (!interruptBrowserDetectActive) return;
    hadAnyResult = true;

    if (interruptBargeInLatched) {
      markBrowserAsrResult("interrupt-live");
      let interimBuf = "";
      for (let i = event.resultIndex; i < event.results.length; i++) {
        const r = event.results[i];
        if (r.isFinal) {
          const piece = r[0].transcript;
          mainBrowserFinalTranscript += piece;
          logPartialAsrSegmentFinal(piece.trim(), { mode: "interrupt-live" });
        } else {
          interimBuf += r[0].transcript;
        }
      }
      mainBrowserLastInterim = interimBuf;
      hasSpoken =
        mainBrowserFinalTranscript.trim().length > 0 || interimBuf.trim().length > 0;
      if (hasSpoken && speechWaitTimeoutId != null) {
        clearTimeout(speechWaitTimeoutId);
        speechWaitTimeoutId = null;
      }
      updateMainBrowserLiveBubble(mainBrowserFinalTranscript, interimBuf);
      interruptPartialLastText = (mainBrowserFinalTranscript + interimBuf).trim();
      scheduleMainBrowserEndOfUtterance();
      return;
    }

    let finalP = "";
    let interim = "";
    for (let i = 0; i < event.results.length; i++) {
      const r = event.results[i];
      if (r.isFinal) {
        finalP += r[0].transcript;
      } else {
        interim += r[0].transcript;
      }
    }
    const combined = (finalP + interim).trim();
    const now = performance.now();
    if (combined.length < 1) {
      if (
        interruptPartialLastChangeAt &&
        now - interruptPartialLastChangeAt > browserAsrInterruptGapMs
      ) {
        interruptPartialAccumMs = 0;
        interruptPartialLastText = "";
      }
      interruptPartialRafTime = now;
      return;
    }

    if (combined !== lastCombined) {
      if (interruptPartialLastChangeAt > 0) {
        const d = Math.min(Math.max(now - interruptPartialLastChangeAt, 0), 250);
        interruptPartialAccumMs += d;
      } else {
        interruptPartialAccumMs = 0;
      }
      interruptPartialLastChangeAt = now;
      lastCombined = combined;
      interruptPartialLastText = combined;
      markBrowserAsrResult("interrupt-detect");

      updateInterruptDetectionBubble(combined);

      const wc = countSpeechWords(combined);
      lastInterruptProbe = {
        interruptGate: "browser_partial_asr_words",
        interruptReason: "browser_partial_asr_words",
        wordCount: wc,
        minWords: interruptBrowserMinWords,
        partialAccumMs: interruptPartialAccumMs,
        sustainMs: browserAsrInterruptSustainMs,
        partialText: combined,
      };

      const wordGate = wc >= interruptBrowserMinWords;
      const sustainGate = wc >= 1 && interruptPartialAccumMs >= browserAsrInterruptSustainMs;
      if (wordGate || sustainGate) {
        onBrowserInterruptBargeInFromDetect(event);
        interruptPartialRafTime = now;
        return;
      }
    } else if (
      interruptPartialLastChangeAt &&
      now - interruptPartialLastChangeAt > browserAsrInterruptGapMs
    ) {
      interruptPartialAccumMs = 0;
    }
    interruptPartialRafTime = now;
  };

  interruptDetectRecognition.onend = () => {
    if (interruptDetectNoResultWatchdogTimer != null) {
      clearTimeout(interruptDetectNoResultWatchdogTimer);
      interruptDetectNoResultWatchdogTimer = null;
    }
    logBrowserAsrStuckEvent("interrupt_detect onend", {
      note: "detector SR ended; barge-in live stream uses same object until abort",
    });
    interruptBrowserDetectActive = false;
    interruptDetectRecognition = null;
  };

  interruptDetectRecognition.onerror = (ev) => {
    if (browserAsrStuckDebugEnabled()) {
      logBrowserAsrStuckEvent("interrupt_detect onerror", {
        error: ev.error,
        message: ev.message,
      });
    }
    if (isFatalBrowserSpeechError(ev.error)) {
      disableBrowserAsrForSession(ev.error);
      try {
        interruptDetectRecognition?.abort();
      } catch {}
      interruptDetectRecognition = null;
      interruptBrowserDetectActive = false;
    }
  };

  try {
    interruptDetectRecognition.start();
    beginBrowserAsrStuckSession("interrupt-detect");
    interruptDetectNoResultWatchdogTimer = window.setTimeout(() => {
      interruptDetectNoResultWatchdogTimer = null;
      if (hadAnyResult || interruptBargeInLatched) return;
      if (!isAssistantTtsPlaying()) return;
      if (!interruptDetectRecognition) return;
      try {
        interruptDetectRecognition.abort();
      } catch {}
      interruptBrowserDetectActive = false;
      interruptDetectRecognition = null;
    }, 4000);
  } catch (e) {
    interruptBrowserDetectActive = false;
    try {
      interruptDetectRecognition?.abort();
    } catch {}
    interruptDetectRecognition = null;
  }
}

function startPostInterruptBrowserRecognition() {
  const SR = window.SpeechRecognition || window.webkitSpeechRecognition;
  if (!SR) return;

  const seedTranscript = (interruptPartialLastText || "").trim();
  abortBrowserSpeechRecognizers();
  mainBrowserFinalTranscript = seedTranscript;
  mainBrowserFinalizeKind = "interrupt";

  let interimBuf = "";

  postInterruptRecognition = new SR();
  postInterruptRecognition.continuous = true;
  postInterruptRecognition.interimResults = true;
  postInterruptRecognition.lang = getSpeechRecognitionLang();

  postInterruptRecognition.onresult = (event) => {
    markBrowserAsrResult("post-interrupt");
    interimBuf = "";
    for (let i = event.resultIndex; i < event.results.length; i++) {
      const r = event.results[i];
      if (r.isFinal) {
        const piece = r[0].transcript;
        mainBrowserFinalTranscript += piece;
        logPartialAsrSegmentFinal(piece.trim(), { mode: "post-interrupt" });
      } else {
        interimBuf += r[0].transcript;
      }
    }
    mainBrowserLastInterim = interimBuf;
    updateMainBrowserLiveBubble(mainBrowserFinalTranscript, interimBuf);
    scheduleMainBrowserEndOfUtterance();
  };

  postInterruptRecognition.onerror = (ev) => {
    if (browserAsrStuckDebugEnabled()) {
      logBrowserAsrStuckEvent("post-interrupt onerror", {
        error: ev.error,
        message: ev.message,
      });
    }
    if (isFatalBrowserSpeechError(ev.error)) {
      disableBrowserAsrForSession(ev.error);
      stopAllBrowserSpeechRecognizers();
      listening = true;
      startListening();
    }
  };

  postInterruptRecognition.onend = () => {
    logBrowserAsrStuckEvent("post-interrupt onend", {});
    postInterruptRecognition = null;
    mainBrowserRecognition = null;
  };

  mainBrowserRecognition = postInterruptRecognition;

  try {
    postInterruptRecognition.start();
    beginBrowserAsrStuckSession("post-interrupt");
  } catch (e) {
    listening = true;
    startListening();
  }
}

async function finalizeInterruptBrowserTranscript(text) {
  const trimmed = (text || "").trim();
  if (!trimmed) {
    stopAllBrowserSpeechRecognizers();
    listening = true;
    startListening();
    return;
  }

  processing = true;
  requestInFlight = true;
  waveState = "idle";
  setStatus("Thinking", "thinking");

  abortBrowserSpeechRecognizers();

  const formData = new FormData();
  formData.append("transcript", trimmed);
  formData.append("use_browser_asr", "1");
  formData.append("session_id", getSessionId());
  formData.append("client", appModePrefix());
  formData.append("context_snapshot", JSON.stringify(buildClientContextSnapshot()));
  formData.append("mode", "interrupt");
  formData.append(
    "interrupt_debug",
    JSON.stringify({
      probe: lastInterruptProbe,
      browser_partial_asr: true,
      thresholds: {
        INTERRUPT_BROWSER_MIN_WORDS: interruptBrowserMinWords,
        BROWSER_ASR_INTERRUPT_SUSTAIN_MS: browserAsrInterruptSustainMs,
        BROWSER_ASR_INTERRUPT_GAP_MS: browserAsrInterruptGapMs,
      },
    })
  );
  formData.append("stream_tts", shouldStreamTts() ? "1" : "0");

  logVoiceTranscript("final", trimmed, { path: "interrupt-browser-asr" });
  logFinalTranscriptSentToLlm("interrupt-browser-asr", trimmed);
  await runInferInterruptPipeline(formData);
}

/* =========================
   START LISTENING
========================= */

function startListening() {
  if (!listening || processing) return;
  if (listeningMode === "continuous" && inputMuted) {
    showMutedStatusIfIdle();
    updateMuteInputButton();
    return;
  }
  clearSpeechWaitTimerAndDetectRaf();

  if (listeningMode === "continuous" && browserAsrPreferred()) {
    waveState = "listening";
    audioChunks = [];
    hasSpoken = false;
    lastVoiceTime = 0;
    setStatus("Listening…", "recording");
    const stBrowser = uiEl("status");
    if (stBrowser) stBrowser.title = "";
    updateMuteInputButton();
    startMainBrowserRecognitionContinuous();
    return;
  }

  waveState = "listening";
  audioChunks = [];
  hasSpoken = false;
  lastVoiceTime = 0;

  mediaRecorder = new MediaRecorder(micStream);
  mediaRecorder.ondataavailable = e => audioChunks.push(e.data);
  mediaRecorder.onstop = handleUtterance;

  mediaRecorder.start();
  detectSpeech();

  if (MAX_WAIT_FOR_MEDIA_RECORDER_INITIAL_MS > 0) {
    speechWaitTimeoutId = setTimeout(() => {
      speechWaitTimeoutId = null;
      if (!hasSpoken && mediaRecorder.state === "recording") {
        mediaRecorder.stop();
      }
    }, MAX_WAIT_FOR_MEDIA_RECORDER_INITIAL_MS);
  }

  updateMuteInputButton();
  setStatus("Listening…", "recording");
  const stEl = uiEl("status");
  if (stEl) {
    stEl.title =
      "Partial text needs Web Speech (HTTPS + a supported browser). Otherwise audio is sent after you pause speaking.";
  }
}

/* =========================
   INFER PIPELINE (shared: recorded audio or browser transcript)
========================= */

async function runInferMainPipeline(formData, opts = {}) {
  try {
    logVoicePipe("POST /infer starting (main, upload in flight)");
    const inferFetchStart = performance.now();
    const inferSignal = opts.signal ?? attachPipelineAbortSignal();
    const serializeTtsPlayback = Boolean(opts.serializeTtsPlayback);
    const res = await fetch(`${API_URL}/infer`, {
      method: "POST",
      body: formData,
      signal: inferSignal
    });
    const inferTtfbMs = performance.now() - inferFetchStart;
    logVoicePipe("POST /infer response headers (main — TTFB)");

    if (shouldStreamTts() && res.ok && isNdjsonTtsResponse(res)) {
      requestInFlight = false;

      let ndjsonMeta = null;
      const streamReplyState = createNdjsonStreamingReplyState();
      void (async () => {
        try {
          console.log("[UX][TTS] NDJSON streaming (main)");
          const playTask = async () => {
            const playbackEnd = await waitForAssistantPlaybackEnd(() => {
              resumeAfterAssistantReplyPlayback();
            });
            resetAudioHandlers();
            await runNdjsonTtsPlayback(res, {
              onMeta: (meta) => {
                ndjsonMeta = { ...ndjsonMeta, ...meta };
                if (meta.transcript) {
                  applyNdjsonUserTranscriptBubble(meta.transcript, "main-ndjson");
                }
              },
              onReplyProgress: (replySoFar) => {
                applyNdjsonStreamingReplySoFar(replySoFar, streamReplyState);
              },
              onDone: (done) => {
                logInferLatency(done, "main", inferTtfbMs);
                finalizeNdjsonStreamingReply(ndjsonMeta, done, streamReplyState);
              },
              onPlayStart: () => {
                logVoiceFirstAudio("main-reply");
                logVoiceMainReplyAudio();
                applyActionPayload(ndjsonMeta);
                waveState = "speaking";
                audioStartedAt = performance.now();
                setStatus(
                  listeningMode === "ptt"
                    ? "Speaking"
                    : "Speaking… (Interruptible)",
                  "speaking"
                );
                startInterruptCapture();
              },
              onPlayEnd: () => {
                playbackEnd.wrappedOnFinish();
              }
            });
            await playbackEnd.donePromise;
          };
          if (serializeTtsPlayback) await enqueueAssistantTtsPlayback(playTask);
          else await playTask();
        } catch (e) {
          if (e?.name !== "AbortError") {
            console.warn("[UX][TTS] NDJSON main playback failed", e);
            processing = false;
            requestInFlight = false;
            voiceUxTurn = null;
            if (listeningMode === "continuous" && listening && !inputMuted) {
              setStatus("Reply playback failed — try again", "offline");
              startListening();
            } else {
              setStatus("Ready", "idle");
            }
            updateMuteInputButton();
          }
        }
      })();
      return;
    }

    const data = await res.json();
    logInferLatency(data, "main", inferTtfbMs);
    requestInFlight = false;

    if (data.skip) {
      hideSidePanel();
      processing = false;
      getAudioEl()?.pause();

      if (listeningMode === "ptt") {
        setStatus("No voice detected", "idle");
      } else if (listeningMode === "continuous") {
        startListening();
      }

      return;
    }

    if (data.client_action === "mute_input") {
      hideSidePanel();
      voiceUxTurn = null;
      getAudioEl()?.pause();
      processing = false;
      setContinuousInputMuted(true);
      return;
    }
    applyClientUiAction(data.client_action);

    commitServerUserTranscriptBubble(data.transcript, "main-json");
    const playMainAnswer = () => {
      resetAudioHandlers();
      void (async () => {
        try {
          const playTask = async () => {
            const playbackEnd = await waitForAssistantPlaybackEnd(() => {
              resumeAfterAssistantReplyPlayback();
            });
            await playTtsFromApi(data, {
              onPlayStart: () => {
                logVoiceFirstAudio("main-reply");
                logVoiceMainReplyAudio();
                applyAssistantReplyAndPanels(data);
                waveState = "speaking";
                audioStartedAt = performance.now();
                setStatus(
                  listeningMode === "ptt"
                    ? "Speaking"
                    : "Speaking… (Interruptible)",
                  "speaking"
                );
                startInterruptCapture();
              },
              onPlayEnd: () => {
                playbackEnd.wrappedOnFinish();
              }
            });
            await playbackEnd.donePromise;
          };
          if (serializeTtsPlayback) await enqueueAssistantTtsPlayback(playTask);
          else await playTask();
        } catch (e) {
          console.warn(e);
        }
      })();
    };

    playMainAnswer();
  } catch (e) {
    if (e?.name === "AbortError") {
      hideSidePanel();
      processing = false;
      requestInFlight = false;
      return;
    }
    hideSidePanel();
    processing = false;
    requestInFlight = false;
    setStatus("Server error", "offline");
  }
}

async function runInferInterruptPipeline(formData) {
  try {
    logVoicePipe("POST /infer starting (interrupt, upload in flight)");
    const inferFetchStart = performance.now();
    const res = await fetch(`${API_URL}/infer`, {
      method: "POST",
      body: formData,
      signal: attachPipelineAbortSignal()
    });
    const inferTtfbMs = performance.now() - inferFetchStart;
    logVoicePipe("POST /infer response headers (interrupt)");

    if (shouldStreamTts() && res.ok && isNdjsonTtsResponse(res)) {
      requestInFlight = false;

      const runStream = async () => {
        let ndjsonMeta = null;
        const streamReplyState = createNdjsonStreamingReplyState();
        resetAudioHandlers();
        try {
          await runNdjsonTtsPlayback(res, {
            onMeta: (meta) => {
              ndjsonMeta = { ...ndjsonMeta, ...meta };
              if (meta.transcript) {
                applyNdjsonUserTranscriptBubble(meta.transcript, "interrupt-ndjson");
              }
            },
            onReplyProgress: (replySoFar) => {
              applyNdjsonStreamingReplySoFar(replySoFar, streamReplyState);
            },
            onDone: (done) => {
              logInferLatency(done, "interrupt", inferTtfbMs);
              finalizeNdjsonStreamingReply(ndjsonMeta, done, streamReplyState);
            },
            onPlayStart: () => {
              logVoiceFirstAudio("main-reply");
              logVoiceMainReplyAudio();
              applyActionPayload(ndjsonMeta);
              waveState = "speaking";
              audioStartedAt = performance.now();
              setStatus("Speaking… (can only be interrupted once)", "speaking");
              processing = false;
            },
            onPlayEnd: () => {
              resumeListeningAfterInterruptPlayback();
            }
          });
        } catch (e) {
          if (e?.name !== "AbortError") console.warn(e);
        }
      };

      await runStream();
      return;
    }

    const data = await res.json();
    logInferLatency(data, "interrupt", inferTtfbMs);

    requestInFlight = false;

    if (data.skip) {
      hideSidePanel();
      processing = false;
      getAudioEl()?.pause();
      if (listeningMode === "ptt") {
        listening = false;
        waveState = "idle";
        setStatus("Ready", "idle");
        updateMuteInputButton();
        return;
      }
      listening = true;
      startListening();
      return;
    }

    if (data.client_action === "mute_input") {
      hideSidePanel();
      getAudioEl()?.pause();
      processing = false;
      listening = true;
      setContinuousInputMuted(true);
      return;
    }
    applyClientUiAction(data.client_action);

    commitServerUserTranscriptBubble(data.transcript, "interrupt-json");

    await playInterruptAnswer(data);
  } catch (e) {
    if (e?.name === "AbortError") {
      hideSidePanel();
      requestInFlight = false;
      processing = false;
      return;
    }
    hideSidePanel();
    requestInFlight = false;
    setStatus("Server error", "offline");
    listening = true;
  }
}

/* =========================
   HANDLE UTTERANCE
========================= */

async function handleUtterance() {
  if (suppressNextUtterance) {
    suppressNextUtterance = false;
    processing = false;
    audioChunks = [];
    hasSpoken = false;
    voiceUxTurn = null;
    showMutedStatusIfIdle();
    return;
  }

  if (listeningMode === "continuous" && inputMuted) {
    processing = false;
    audioChunks = [];
    hasSpoken = false;
    voiceUxTurn = null;
    showMutedStatusIfIdle();
    return;
  }

  if (listeningMode === "continuous" && !hasSpoken) {
    processing = false;
    voiceUxTurn = null;
    startListening();
    return;
  }

  const blob = new Blob(audioChunks, { type: "audio/webm" });

  if (blob.size < MIN_AUDIO_BYTES) {
    processing = false;
    voiceUxTurn = null;

    if (listeningMode === "continuous") {
      startListening();
    }

    return;
  }
  requestInFlight = true;
  processing = true;
  waveState = "idle";

  setStatus("Thinking", "thinking");

  const formData = new FormData();
  formData.append("audio", blob);
  formData.append("session_id", getSessionId());
  formData.append("client", appModePrefix());
  formData.append("context_snapshot", JSON.stringify(buildClientContextSnapshot()));

  // 🔑 ADD THIS
  if (listeningMode === "ptt") {
    formData.append("mode", "ptt");
  }
  formData.append("stream_tts", shouldStreamTts() ? "1" : "0");

  await runInferMainPipeline(formData);
}

/* =========================
   TEXT INPUT PIPELINE
========================= */

/**
 * Work mode: typed lines use the same `/infer` path as browser-ASR voice (including optional
 * reasoning-stream prep via maybePrepareWorkModeReasoning), not the separate `/text` handler.
 */
async function sendVeraWorkModeTypedInferTurn(text, opts = {}) {
  const trimmed = String(text ?? "").trim();
  const path = opts.path || "work-typed";
  const fromQueue = Boolean(opts.__fromQueue);
  if (!trimmed || !isVeraWorkModeOn() || appModePrefix() !== "vera") return;
  if (await maybeHandleWorkChecklistPlanShortcut(trimmed)) return;

  const statusLine = uiEl("status");
  if (statusLine?.classList.contains("offline")) {
    requestInFlight = false;
    processing = false;
    listening = false;
    setStatus("Ready", "idle");
  }

  if (isWorkModeTypedTurnBlocked()) {
    if (!fromQueue) {
      const queued = enqueueWorkModeTypedTurn(trimmed, opts);
      if (!queued) setStatus("Work queue full (max 3)", "idle");
    }
    return;
  }

  /* User bubble: do not addBubble here — /infer NDJSON first `asr` line calls commitServerUserTranscriptBubble
     (same as voice). A prior addBubble would duplicate the row in Voice UI. */
  ensureChatStartedLayout();

  listening = false;
  processing = true;
  requestInFlight = true;
  waveState = "idle";
  setStatus("Thinking", "thinking");
  beginVoiceUxTurn();

  const formData = new FormData();
  formData.append("transcript", trimmed);
  formData.append("use_browser_asr", "1");
  formData.append("session_id", getSessionId());
  formData.append("client", appModePrefix());
  formData.append("context_snapshot", JSON.stringify(buildClientContextSnapshot()));
  formData.append("stream_tts", shouldStreamTts() ? "1" : "0");
  if (opts.reasoningAttachment instanceof File && opts.reasoningAttachment.size > 0) {
    const f = opts.reasoningAttachment;
    /* Clone bytes so the same File object can be read again by reasoning_stream_upload without edge-case stream reuse. */
    const forInfer = f.slice(0, f.size, f.type || undefined);
    formData.append("context_file", forInfer, f.name || "upload");
  }
  if (listeningMode === "ptt") {
    formData.append("mode", "ptt");
  }

  logFinalTranscriptSentToLlm(path, trimmed);

  const pipelineSig = attachPipelineAbortSignal();
  try {
    const prep = await maybePrepareWorkModeReasoning(formData, trimmed, pipelineSig, {
      attachment: opts.reasoningAttachment || null
    });
    if (prep === "reasoning-upload-failed") {
      processing = false;
      requestInFlight = false;
      voiceUxTurn = null;
      setStatus("Ready", "idle");
      return;
    }
    await runInferMainPipeline(formData, { signal: pipelineSig, serializeTtsPlayback: true });
  } catch (err) {
    if (err?.name === "AbortError") {
      processing = false;
      requestInFlight = false;
      voiceUxTurn = null;
      return;
    }
    console.warn("[WorkMode] typed infer", err);
    hideSidePanel();
    processing = false;
    requestInFlight = false;
    voiceUxTurn = null;
    setStatus("Server error", "offline");
  } finally {
    if (workModeTypedTurnQueue.length > 0 && !isWorkModeTypedTurnBlocked()) {
      scheduleWorkModeTypedQueueDrain();
    }
  }
}

async function sendTextMessage() {
  const textInput = uiEl("text-input");
  const statusLine = uiEl("status");
  const text = textInput?.value.trim() ?? "";
  const inVeraWorkMode = isVeraWorkModeOn() && appModePrefix() === "vera";

  // 🔑 recover from offline
  if (statusLine?.classList.contains("offline")) {
    requestInFlight = false;
    processing = false;
    listening = false;
    setStatus("Ready", "idle");
  }

  if (!text) return;
  if (inVeraWorkMode) {
    if (textInput) textInput.value = "";
    await sendVeraWorkModeTypedInferTurn(text, { path: "typed-text" });
    return;
  }
  const consecutiveUserTail = (() => {
    const convo = uiEl("conversation");
    if (!convo) return 0;
    const rows = [...convo.querySelectorAll(".message-row")];
    let count = 0;
    for (let i = rows.length - 1; i >= 0; i -= 1) {
      const row = rows[i];
      if (!(row instanceof HTMLElement)) continue;
      const bubble = row.querySelector(".bubble");
      if (bubble instanceof HTMLElement && bubble.classList.contains("interrupt-preview")) continue;
      if (row.classList.contains("user")) {
        count += 1;
        continue;
      }
      break;
    }
    return count;
  })();
  if (consecutiveUserTail >= 3) {
    setStatus("Wait for VERA response before sending more", "idle");
    console.warn("[Keyboard] blocked after 3 pending user turns");
    return;
  }
  if (isServerPipelineBusy() && isFlowModeKeyboardInterruptAllowed()) {
    interruptAssistantPipelineForTypedMessage();
  }

  if (isServerPipelineBusy()) return;
  if (textInput) textInput.value = "";

  beginTextUxTurn();
  listening = false;
  processing = true;
  requestInFlight = true;
  waveState = "idle";

  setStatus("Thinking", "thinking");

  addBubble(text, "user", { path: "typed-text" });
  ensureChatStartedLayout();
  try {
    const textFetchStart = performance.now();
    const res = await fetch(`${API_URL}/text`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        text,
        session_id: getSessionId(),
        client: appModePrefix(),
        stream_tts: shouldStreamTts(),
        context_snapshot: buildClientContextSnapshot()
      }),
      signal: attachPipelineAbortSignal()
    });
    const textTtfbMs = performance.now() - textFetchStart;

    if (shouldStreamTts() && res.ok && isNdjsonTtsResponse(res)) {
      requestInFlight = false;

      let ndjsonMeta = null;
      const streamReplyState = createNdjsonStreamingReplyState();
      void (async () => {
        try {
          console.log("[UX][TTS] NDJSON streaming (text)");
          resetAudioHandlers();
          await runNdjsonTtsPlayback(res, {
            onMeta: (meta) => {
              ndjsonMeta = { ...ndjsonMeta, ...meta };
            },
            onReplyProgress: (replySoFar) => {
              applyNdjsonStreamingReplySoFar(replySoFar, streamReplyState);
            },
            onDone: (done) => {
              logInferLatency(done, "text", textTtfbMs);
              finalizeNdjsonStreamingReply(ndjsonMeta, done, streamReplyState);
            },
            onPlayStart: () => {
              logTextFirstAudio("main-reply");
              logTextMainReplyAudio();
              applyActionPayload(ndjsonMeta);
              waveState = "speaking";
              audioStartedAt = performance.now();
              setStatus(
                listeningMode === "ptt" ? "Speaking" : "Speaking…",
                "speaking"
              );
            },
            onPlayEnd: () => {
              resumeAfterAssistantReplyPlayback();
            }
          });
        } catch (e) {
          if (e?.name !== "AbortError") console.warn(e);
        }
      })();
      return;
    }

    const data = await res.json();
    logInferLatency(data, "text", textTtfbMs);

    requestInFlight = false;
    applyClientUiAction(data.client_action);

    const playReply = () => {
      resetAudioHandlers();
      void (async () => {
        try {
          await playTtsFromApi(data, {
            onPlayStart: () => {
              logTextFirstAudio("main-reply");
              logTextMainReplyAudio();
              applyAssistantReplyAndPanels(data);
              waveState = "speaking";
              audioStartedAt = performance.now();
              setStatus(
                listeningMode === "ptt" ? "Speaking" : "Speaking…",
                "speaking"
              );
            },
            onPlayEnd: () => {
              resumeAfterAssistantReplyPlayback();
            }
          });
        } catch (e) {
          console.warn(e);
        }
      })();
    };

    playReply();

  } catch (err) {
    if (err?.name === "AbortError") {
      requestInFlight = false;
      processing = false;
      textUxTurn = null;
      return;
    }
    console.error(err);
    hideSidePanel();
    requestInFlight = false;
    processing = false;
    textUxTurn = null;
    setStatus("Server error", "offline");
  }
}

/* =========================
   MIC BUTTON
========================= */
async function beginPttRecordingNow() {
  stopActiveMicCaptureSilently();
  listeningMode = "ptt";
  updateMuteInputButton();
  pttRecording = true;
  await initMic();
  micStream?.getAudioTracks().forEach((track) => {
    track.enabled = true;
  });
  listening = true;
  processing = false;
  waveState = "listening";
  audioChunks = [];
  hasSpoken = false;
  lastVoiceTime = 0;

  if (browserAsrPreferred()) {
    mainBrowserFinalizeKind = "main";
    startMainBrowserRecognitionContinuous();
    setStatus("Listening (PTT)", "recording");
    return;
  }

  mediaRecorder = new MediaRecorder(micStream);
  mediaRecorder.ondataavailable = (e) => audioChunks.push(e.data);
  mediaRecorder.onstop = handleUtterance;
  mediaRecorder.start();
  setStatus("Listening (PTT)", "recording");
}

async function onPttClick() {
  ensureChatStartedLayout();
  if (isServerPipelineBusy()) {
    cancelVoicePipelineAndResetState();
    await beginPttRecordingNow();
    return;
  }
  if (!pttRecording) {
    await beginPttRecordingNow();
    return;
  }
  pttRecording = false;
  listening = false;
  waveState = "idle";

  if (browserAsrPreferred()) {
    const text = (
      mainBrowserFinalTranscript + (mainBrowserLastInterim || "")
    ).trim();
    stopAllBrowserSpeechRecognizers();
    if (!text) {
      setStatus("Ready", "idle");
      updateMuteInputButton();
      return;
    }
    if (await maybeHandleWorkChecklistPlanShortcut(text)) {
      setStatus("Ready", "idle");
      updateMuteInputButton();
      return;
    }
    removeMainBrowserLiveBubble();
    beginVoiceUxTurn();
    requestInFlight = true;
    processing = true;
    waveState = "idle";
    setStatus("Thinking", "thinking");
    const formData = new FormData();
    formData.append("transcript", text);
    formData.append("use_browser_asr", "1");
    formData.append("session_id", getSessionId());
    formData.append("client", appModePrefix());
    formData.append("context_snapshot", JSON.stringify(buildClientContextSnapshot()));
    formData.append("mode", "ptt");
    formData.append("stream_tts", shouldStreamTts() ? "1" : "0");
    logVoiceTranscript("final", text, { path: "ptt-browser-asr" });
    logFinalTranscriptSentToLlm("ptt-browser-asr", text);
    void (async () => {
      try {
        attachPipelineAbortSignal();
        const pipelineSig = activePipelineAbort.signal;
        await maybePrepareWorkModeReasoning(formData, text, pipelineSig);
        await runInferMainPipeline(formData, { signal: pipelineSig });
      } catch (err) {
        if (err?.name !== "AbortError") {
          console.warn("[PTT][browser-asr] infer", err);
        }
      }
    })();
    return;
  }

  if (mediaRecorder && mediaRecorder.state === "recording") {
    beginVoiceUxTurn();
    mediaRecorder.stop();
  }
}

["vera-ptt", "bmo-ptt"].forEach((id) => {
  document.getElementById(id)?.addEventListener("click", onPttClick);
});

async function onRecordClick() {
  ensureChatStartedLayout();
  browserAsrMainNetworkRetries = 0;
  listeningMode = "continuous";
  updateMuteInputButton();

  if (isServerPipelineBusy() || pttRecording) {
    cancelVoicePipelineAndResetState();
    inputMuted = false;
    await initMic();
    micStream?.getAudioTracks().forEach((track) => {
      track.enabled = true;
    });
    listening = true;
    updateMuteInputButton();
    startListening();
    return;
  }

  if (!listening) {
    inputMuted = false;
    await initMic();
    micStream?.getAudioTracks().forEach((track) => {
      track.enabled = true;
    });
    listening = true;
    updateMuteInputButton();
    startListening();
    return;
  }

  if (listeningMode !== "continuous" || !micStream) return;
  setContinuousInputMuted(!inputMuted);
}

["vera-record", "bmo-record"].forEach((id) => {
  document.getElementById(id)?.addEventListener("click", onRecordClick);
});

updateMuteInputButton();
wireMobileInterruptDebugUi();

document.addEventListener("visibilitychange", () => {
  if (document.visibilityState !== "visible") return;
  if (browserAsrVisibilityResumeTimer != null) {
    clearTimeout(browserAsrVisibilityResumeTimer);
    browserAsrVisibilityResumeTimer = null;
  }
  browserAsrVisibilityResumeTimer = window.setTimeout(() => {
    browserAsrVisibilityResumeTimer = null;
    maybeResumeMainBrowserSpeechRecognition("tab-visible");
  }, 280);
});

if (!IS_MOBILE) {
  ["vera", "bmo"].forEach((prefix) => {
    const sendTextBtn = document.getElementById(`${prefix}-send-text`);
    const textInput = document.getElementById(`${prefix}-text-input`);
    sendTextBtn?.addEventListener("click", sendTextMessage);
    textInput?.addEventListener("keydown", (e) => {
      if (e.key === "Enter") {
        sendTextMessage();
      }
    });
  });
}

/* =========================
   FEEDBACK
========================= */

if (sendFeedbackBtn) {
  sendFeedbackBtn.onclick = async () => {
    const text = feedbackInput.value.trim();
    if (!text) return;

    feedbackStatusEl.textContent = "Sending…";
    feedbackStatusEl.style.color = "";

    try {
      const res = await fetch(`${API_URL}/feedback`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({
          session_id: getSessionId(),
          feedback: text,
          userAgent: navigator.userAgent,
          timestamp: new Date().toISOString()
        })
      });

      if (!res.ok) throw new Error();

      feedbackInput.value = "";
      feedbackStatusEl.textContent = "Thank you for your feedback!";
      feedbackStatusEl.style.color = "#5cffb1";
    } catch {
      feedbackStatusEl.textContent = "Failed to send feedback.";
      feedbackStatusEl.style.color = "#ff6b6b";
    }
  };
}

window.resetVoiceUiToIdle = cancelVoicePipelineAndResetState;

/* =========================
   HIDDEN USER SIGN-IN (long-press VERA logo 2s)
========================= */

/**
 * Base URL for FastAPI user routes (sign-in, /api/user/active).
 * GitHub Pages / static hosts cannot serve POST /api — must use API_URL (Worker → tunnel → app.py).
 * Order: explicit override → localhost uvicorn → meta → file → API_URL for all other https origins.
 */
function localBackendBase() {
  if (typeof window !== "undefined" && window.VERA_LOCAL_BACKEND_ORIGIN) {
    return String(window.VERA_LOCAL_BACKEND_ORIGIN).replace(/\/$/, "");
  }
  const o = typeof window !== "undefined" ? window.location?.origin : "";
  if (o && o !== "null" && !o.startsWith("file:")) {
    const isLocal =
      /^https?:\/\/(localhost|127\.0\.0\.1)(:\d+)?$/i.test(o) ||
      /^https?:\/\/\[::1\](:\d+)?$/i.test(o);
    if (isLocal) return o.replace(/\/$/, "");
  }
  const m = document.querySelector('meta[name="vera-local-backend-origin"]');
  const meta = m?.content?.trim();
  if (meta) return meta.replace(/\/$/, "");
  if (!o || o === "null" || o.startsWith("file:")) {
    return "http://127.0.0.1:8000";
  }
  const remote = String(API_URL).replace(/\/$/, "");
  return remote || "https://vera-api.vera-api-ned.workers.dev";
}

function authApiBase() {
  return localBackendBase();
}

/** Absolute URL for user auth; never same-origin relative /api/... on GitHub Pages. */
function authApiUrl(path) {
  const p = path.startsWith("/") ? path : `/${path}`;
  let base = localBackendBase();
  if (!base || !String(base).trim()) {
    base = String(API_URL).replace(/\/$/, "") || "https://vera-api.vera-api-ned.workers.dev";
  }
  const root = String(base).replace(/\/$/, "");
  return new URL(p, `${root}/`).href;
}

function setVeraActiveUserLabel(usernameOrNull) {
  const el = document.getElementById("vera-active-user-label");
  if (!el) return;
  if (usernameOrNull == null || usernameOrNull === "") {
    el.textContent = "";
    el.setAttribute("hidden", "");
    return;
  }
  el.textContent = `user: ${usernameOrNull}`;
  el.removeAttribute("hidden");
}

async function refreshVeraActiveUserLabel() {
  const tabUser = sessionStorage.getItem(VERA_TAB_ACTIVE_USER_KEY) || "";
  if (!tabUser) {
    setVeraActiveUserLabel(null);
    try {
      await fetch(authApiUrl("/api/user/sign-out"), { method: "POST" });
    } catch {}
    return;
  }
  try {
    const res = await fetch(authApiUrl("/api/user/active"), { method: "GET" });
    const data = await res.json().catch(() => ({}));
    if (!res.ok) {
      setVeraActiveUserLabel(null);
      return;
    }
    const activeName = data.username != null && data.username !== "" ? String(data.username) : tabUser;
    setVeraActiveUserLabel(activeName || null);
  } catch {
    setVeraActiveUserLabel(tabUser || null);
  }
}

function wireVeraSettingsPanel() {
  const modal = document.getElementById("vera-settings-modal");
  const openVeraBtn = document.getElementById("vera-settings-open");
  const openBmoBtn = document.getElementById("bmo-settings-open");
  const closeBtn = document.getElementById("vera-settings-close");
  const silenceSlider = document.getElementById("vera-setting-silence");
  const asrStreamingBtn = document.getElementById("vera-setting-asr-streaming");
  const asrSingleBtn = document.getElementById("vera-setting-asr-single");
  const mainPartialMinSel = document.getElementById("vera-setting-main-partial-min");
  const resetSessionBtn = document.getElementById("vera-setting-reset-session");
  const workModeMuteBtn = document.getElementById("vera-setting-workmode-mute");
  const saveBtn = document.getElementById("vera-settings-save");
  if (!(modal instanceof HTMLElement)) return;

  const silenceOptions = [1000, 1300, 1600];
  let draftSilenceMs = getVeraAsrSilenceMs();
  let draftAsrMode = getVeraAsrMode();
  let draftWorkModeMute = isWorkModeMuteEnabled();
  let draftMainAsrPartialMinChars = getMainAsrPartialMinChars();
  const partialMinCharOptions = [5, 8, 10, 12, 15];
  const silenceToIndex = (ms) => {
    const idx = silenceOptions.indexOf(ms);
    return idx >= 0 ? idx : 1;
  };
  const readSliderSilenceMs = () => {
    if (!(silenceSlider instanceof HTMLInputElement)) return draftSilenceMs;
    const raw = Number(silenceSlider.value);
    const idx = Number.isFinite(raw) ? Math.max(0, Math.min(2, raw)) : 1;
    return silenceOptions[idx];
  };
  const partialMinCharsToIndex = (n) => {
    const idx = partialMinCharOptions.indexOf(n);
    return idx >= 0 ? idx : 2;
  };
  const readSliderPartialMinChars = () => {
    if (!(mainPartialMinSel instanceof HTMLInputElement)) return draftMainAsrPartialMinChars;
    const raw = Number(mainPartialMinSel.value);
    const idx = Number.isFinite(raw) ? Math.max(0, Math.min(partialMinCharOptions.length - 1, raw)) : 2;
    return partialMinCharOptions[idx];
  };

  const applyAsrModeUi = (mode) => {
    const streamingOn = mode !== "single";
    if (asrStreamingBtn instanceof HTMLButtonElement) {
      asrStreamingBtn.classList.toggle("is-active", streamingOn);
      asrStreamingBtn.setAttribute("aria-pressed", streamingOn ? "true" : "false");
    }
    if (asrSingleBtn instanceof HTMLButtonElement) {
      asrSingleBtn.classList.toggle("is-active", !streamingOn);
      asrSingleBtn.setAttribute("aria-pressed", !streamingOn ? "true" : "false");
    }
  };

  const applyMuteUi = () => {
    const on = draftWorkModeMute;
    if (workModeMuteBtn instanceof HTMLButtonElement) {
      workModeMuteBtn.classList.toggle("is-on", on);
      workModeMuteBtn.setAttribute("aria-pressed", on ? "true" : "false");
    }
  };

  const hydrate = () => {
    draftSilenceMs = getVeraAsrSilenceMs();
    draftAsrMode = getVeraAsrMode();
    draftWorkModeMute = isWorkModeMuteEnabled();
    draftMainAsrPartialMinChars = getMainAsrPartialMinChars();
    if (silenceSlider instanceof HTMLInputElement) {
      silenceSlider.value = String(silenceToIndex(draftSilenceMs));
    }
    if (mainPartialMinSel instanceof HTMLInputElement) {
      mainPartialMinSel.value = String(partialMinCharsToIndex(draftMainAsrPartialMinChars));
    }
    applyAsrModeUi(draftAsrMode);
    applyMuteUi();
    applyVeraWorkModeMuteSetting();
  };

  const open = () => {
    hydrate();
    logVeraSettings("open_modal", {
      silence_ms: draftSilenceMs,
      asr_mode: draftAsrMode,
      workmode_mute: draftWorkModeMute ? 1 : 0,
      main_asr_partial_min_chars: draftMainAsrPartialMinChars,
    });
    modal.removeAttribute("hidden");
  };
  const close = () => {
    modal.setAttribute("hidden", "");
  };

  openVeraBtn?.addEventListener("click", open);
  openBmoBtn?.addEventListener("click", open);
  closeBtn?.addEventListener("click", close);
  modal.addEventListener("click", (e) => {
    if (e.target === modal) close();
  });

  const syncDraftSilenceFromSlider = () => {
    draftSilenceMs = readSliderSilenceMs();
    logVeraSettings("draft_silence_ms", { value: draftSilenceMs });
  };
  silenceSlider?.addEventListener("input", syncDraftSilenceFromSlider);
  silenceSlider?.addEventListener("change", syncDraftSilenceFromSlider);
  asrStreamingBtn?.addEventListener("click", () => {
    draftAsrMode = "streaming";
    applyAsrModeUi("streaming");
    logVeraSettings("draft_asr_mode", { value: draftAsrMode });
  });
  asrSingleBtn?.addEventListener("click", () => {
    draftAsrMode = "single";
    applyAsrModeUi("single");
    logVeraSettings("draft_asr_mode", { value: draftAsrMode });
  });
  const syncDraftPartialMinChars = () => {
    draftMainAsrPartialMinChars = readSliderPartialMinChars();
    logVeraSettings("draft_main_asr_partial_min_chars", { value: draftMainAsrPartialMinChars });
  };
  mainPartialMinSel?.addEventListener("input", syncDraftPartialMinChars);
  mainPartialMinSel?.addEventListener("change", syncDraftPartialMinChars);
  workModeMuteBtn?.addEventListener("click", () => {
    draftWorkModeMute = !draftWorkModeMute;
    applyMuteUi();
    logVeraSettings("draft_workmode_mute", { value: draftWorkModeMute ? 1 : 0 });
  });
  saveBtn?.addEventListener("click", () => {
    draftSilenceMs = readSliderSilenceMs();
    draftMainAsrPartialMinChars = readSliderPartialMinChars();
    logVeraSettings("save_click", {
      silence_ms: draftSilenceMs,
      asr_mode: draftAsrMode,
      workmode_mute: draftWorkModeMute ? 1 : 0,
      main_asr_partial_min_chars: draftMainAsrPartialMinChars,
    });
    setVeraAsrSilenceMs(draftSilenceMs);
    setVeraAsrMode(draftAsrMode);
    setMainAsrPartialMinChars(draftMainAsrPartialMinChars);
    setWorkModeMuteEnabled(draftWorkModeMute);
    close();
  });

  resetSessionBtn?.addEventListener("click", () => {
    logVeraSettings("reset_session_click", { mode: appModePrefix() });
    const ok = window.confirm("Start a new session now? This clears current chat and work-mode checklist/reasoning state.");
    if (!ok) return;
    if (appModePrefix() === "bmo") resetBmoSessionAndUi();
    else resetVeraSessionAndUi();
    close();
  });

  const app = document.getElementById("vera-app");
  if (app && typeof MutationObserver !== "undefined") {
    const obs = new MutationObserver(() => applyVeraWorkModeMuteSetting());
    obs.observe(app, { attributes: true, attributeFilter: ["class"] });
  }
  hydrate();
}

function wireVeraUserSignInHoldAndModal() {
  const holdMs = 2000;
  /* Long-press sign-in only in VERA app (#return-home-vera), not on landing nav-home */
  const logos = [document.getElementById("return-home-vera")].filter(Boolean);

  const revealSignInButtons = () => {
    document.getElementById("vera-user-sign-in")?.removeAttribute("hidden");
  };

  logos.forEach((el) => {
    let timer = null;
    let longPress = false;
    let holding = false;
    let rafId = null;
    let holdStart = 0;

    const tick = () => {
      if (!holding) return;
      const elapsed = performance.now() - holdStart;
      const pct = Math.min(100, (elapsed / holdMs) * 100);
      el.style.setProperty("--vera-hold-pct", `${pct}%`);
      if (holding && elapsed < holdMs) {
        rafId = requestAnimationFrame(tick);
      }
    };

    const endHoldTracking = () => {
      holding = false;
      if (rafId != null) {
        cancelAnimationFrame(rafId);
        rafId = null;
      }
      el.style.setProperty("--vera-hold-pct", "0%");
    };

    el.addEventListener("pointerdown", () => {
      longPress = false;
      holding = true;
      holdStart = performance.now();
      timer = window.setTimeout(() => {
        longPress = true;
        revealSignInButtons();
        el.style.setProperty("--vera-hold-pct", "100%");
        holding = false;
        if (rafId != null) {
          cancelAnimationFrame(rafId);
          rafId = null;
        }
      }, holdMs);
      rafId = requestAnimationFrame(tick);
    });

    const cancelTimerAndFill = () => {
      if (timer != null) {
        clearTimeout(timer);
        timer = null;
      }
      endHoldTracking();
    };

    el.addEventListener("pointerup", cancelTimerAndFill);
    el.addEventListener("pointerleave", cancelTimerAndFill);
    el.addEventListener("pointercancel", cancelTimerAndFill);
    el.addEventListener(
      "click",
      (e) => {
        if (longPress) {
          e.preventDefault();
          e.stopImmediatePropagation();
          longPress = false;
        }
      },
      true
    );
  });

  const modal = document.getElementById("vera-user-sign-in-modal");
  const errEl = document.getElementById("vera-sign-in-error");

  const showErr = (msg) => {
    if (!errEl) return;
    errEl.textContent = msg || "";
    errEl.hidden = !msg;
  };

  const openModal = () => {
    showErr("");
    modal?.removeAttribute("hidden");
  };

  const closeModal = () => {
    modal?.setAttribute("hidden", "");
    showErr("");
  };

  document.getElementById("vera-user-sign-in")?.addEventListener("click", openModal);
  document.getElementById("vera-sign-in-cancel")?.addEventListener("click", closeModal);
  modal?.addEventListener("click", (e) => {
    if (e.target === modal) closeModal();
  });

  document.getElementById("vera-sign-in-submit")?.addEventListener("click", async () => {
    const userEl = document.getElementById("vera-sign-in-username");
    const passEl = document.getElementById("vera-sign-in-password");
    const user = userEl?.value?.trim() ?? "";
    const pass = passEl?.value?.trim() ?? "";
    showErr("");
    try {
      const res = await fetch(authApiUrl("/api/user/sign-in"), {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ username: user, password: pass })
      });
      const data = await res.json().catch(() => ({}));
      if (!res.ok) {
        const d = data.detail;
        if (Array.isArray(d) && d.length > 0 && d[0]?.msg) {
          showErr(String(d[0].msg));
          return;
        }
        showErr(typeof d === "string" ? d : "Wrong password or username.");
        return;
      }
      const name = data.username != null && data.username !== "" ? String(data.username) : null;
      if (name) sessionStorage.setItem(VERA_TAB_ACTIVE_USER_KEY, name);
      setVeraActiveUserLabel(name);
      /* Start a fresh VERA session on successful user sign-in. */
      if (typeof window.resetVeraSessionAndUi === "function") {
        window.resetVeraSessionAndUi();
      }
      await hydrateWorkChecklistFromServer(true);
      closeModal();
      if (passEl) passEl.value = "";
    } catch {
      showErr(
        "Could not reach the auth server. If you use GitHub Pages, deploy the latest app.js (cache-busted) so sign-in uses the VERA API URL, or set window.VERA_LOCAL_BACKEND_ORIGIN."
      );
    }
  });
}

wireVeraUserSignInHoldAndModal();
wireVeraSettingsPanel();
refreshVeraActiveUserLabel();

(function stripSpotifyOAuthQueryParams() {
  try {
    const u = new URL(window.location.href);
    if (!u.searchParams.has("spotify_connected") && !u.searchParams.has("spotify_error")) return;
    const err = u.searchParams.get("spotify_error");
    u.searchParams.delete("spotify_connected");
    u.searchParams.delete("spotify_error");
    if (err) console.warn("[Spotify OAuth]", err);
    history.replaceState({}, "", u.pathname + u.search + u.hash);
    try {
      const bc = new BroadcastChannel("vera-spotify");
      bc.postMessage({ type: "spotify-oauth-done", error: err });
      bc.close();
    } catch (_) {
      /* ignore */
    }
  } catch (_) {
    /* ignore */
  }
})();

(function wireSpotifyOAuthPostMessageFromPopup() {
  if (window.__veraSpotifyOAuthPostMessageWired) return;
  window.__veraSpotifyOAuthPostMessageWired = true;
  window.addEventListener("message", (ev) => {
    if (ev.data?.type !== "vera-spotify-oauth") return;
    let apiOrigin;
    try {
      apiOrigin = new URL(localBackendBase()).origin;
    } catch (_) {
      return;
    }
    if (ev.origin !== apiOrigin) return;
    if (!ev.data.ok) {
      console.warn("[Spotify OAuth]", ev.data.error);
      return;
    }
    void (async () => {
      if (ev.data.handoff) await claimSpotifyHandoff(ev.data.handoff);
      void refreshSpotifyPanelAfterOAuthInOtherTab();
    })();
  });
})();

(function wireSpotifyOAuthOtherTabsRefresh() {
  if (window.__veraSpotifyCrossTabWired) return;
  window.__veraSpotifyCrossTabWired = true;
  try {
    const bc = new BroadcastChannel("vera-spotify");
    bc.addEventListener("message", (ev) => {
      if (ev.data?.type !== "spotify-oauth-done") return;
      void refreshSpotifyPanelAfterOAuthInOtherTab();
    });
  } catch (_) {
    /* ignore */
  }
  let focusT;
  const onVisible = () => {
    if (window.__veraSpotifyPlaybackActive) return;
    const s = window.__veraSpotifyNowState;
    if (s && (Number(s.position_ms) > 0 || Number(s.duration_ms) > 0)) return;
    if (!window.__veraSpotifyOAuthPoll) return;
    clearTimeout(focusT);
    focusT = setTimeout(() => void refreshSpotifyPanelAfterOAuthInOtherTab(), 280);
  };
  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "visible") onVisible();
  });
  window.addEventListener("focus", onVisible);
})();

/**
 * Spotify: search (Client Credentials) + optional Web Playback SDK after user connects (Premium).
 */
window.__veraSpotifyLast = { preview_url: "", open_url: "", title: "", artist: "" };

window.VeraSpotify = {
  async searchTracks(query) {
    const raw = String(query || "").trim();
    if (!raw) return [];
    /* Same origin as sign-in: local http://127.0.0.1:8000 uses your .env; GitHub Pages uses API_URL via localBackendBase(). */
    const u = new URL(authApiUrl("/api/spotify/search"));
    u.searchParams.set("q", raw);
    const res = await fetch(u.href, { cache: "no-store" });
    if (!res.ok) {
      let msg = `Search failed (${res.status})`;
      try {
        const err = await res.json();
        const d = err.detail;
        if (typeof d === "string") msg = d;
        else if (Array.isArray(d) && d[0]?.msg) msg = String(d[0].msg);
      } catch (_) {
        /* ignore */
      }
      throw new Error(msg);
    }
    const data = await res.json();
    return Array.isArray(data) ? data : [];
  },
  async getAlbumTracks(albumId) {
    const id = String(albumId || "").trim();
    if (!id) return [];
    const u = new URL(authApiUrl(`/api/spotify/albums/${encodeURIComponent(id)}/tracks`));
    u.searchParams.set("limit", "50");
    const res = await fetch(u.href, { cache: "no-store" });
    if (!res.ok) {
      let msg = `Album tracks failed (${res.status})`;
      try {
        const err = await res.json();
        if (typeof err.detail === "string") msg = err.detail;
      } catch (_) {
        /* ignore */
      }
      throw new Error(msg);
    }
    const data = await res.json();
    return Array.isArray(data) ? data : [];
  },
  async getArtistTopTracks(artistId) {
    const id = String(artistId || "").trim();
    if (!id) return [];
    const u = new URL(authApiUrl(`/api/spotify/artists/${encodeURIComponent(id)}/top-tracks`));
    const res = await fetch(u.href, { cache: "no-store" });
    if (!res.ok) {
      let msg = `Artist top tracks failed (${res.status})`;
      try {
        const err = await res.json();
        if (typeof err.detail === "string") msg = err.detail;
      } catch (_) {
        /* ignore */
      }
      throw new Error(msg);
    }
    const data = await res.json();
    return Array.isArray(data) ? data : [];
  },
  async getArtistAlbums(artistId) {
    const id = String(artistId || "").trim();
    if (!id) return [];
    const u = new URL(authApiUrl(`/api/spotify/artists/${encodeURIComponent(id)}/albums`));
    u.searchParams.set("limit", "200");
    const res = await fetch(u.href, { cache: "no-store" });
    if (!res.ok) {
      let msg = `Artist albums failed (${res.status})`;
      try {
        const err = await res.json();
        if (typeof err.detail === "string") msg = err.detail;
      } catch (_) {
        /* ignore */
      }
      throw new Error(msg);
    }
    const data = await res.json();
    return Array.isArray(data) ? data : [];
  },
  async getPlaylists() {
    const u = new URL(authApiUrl("/api/spotify/me/playlists"));
    u.searchParams.set("limit", "30");
    const res = await fetch(u.href, {
      credentials: "include",
      headers: { ...veraSpotifyAuthHeaders() },
      cache: "no-store"
    });
    if (!res.ok) {
      let msg = `Playlist fetch failed (${res.status})`;
      try {
        const err = await res.json();
        if (typeof err.detail === "string") msg = err.detail;
      } catch (_) {
        /* ignore */
      }
      throw new Error(msg);
    }
    const data = await res.json();
    return Array.isArray(data) ? data : [];
  },
  async getPlaylistTracks(playlistId) {
    const pid = String(playlistId || "").trim();
    if (!pid) return [];
    const u = new URL(authApiUrl(`/api/spotify/playlists/${encodeURIComponent(pid)}/tracks`));
    u.searchParams.set("limit", "100");
    const res = await fetch(u.href, {
      credentials: "include",
      headers: { ...veraSpotifyAuthHeaders() },
      cache: "no-store"
    });
    if (!res.ok) {
      let msg = `Playlist tracks fetch failed (${res.status})`;
      try {
        const err = await res.json();
        if (typeof err.detail === "string") msg = err.detail;
      } catch (_) {
        /* ignore */
      }
      throw new Error(msg);
    }
    const data = await res.json();
    return Array.isArray(data) ? data : [];
  },
  async playTrack(uri, meta) {
    const prefix = appModePrefix();
    const base = localBackendBase();
    const preview = meta?.preview_url;
    const openUrl = String(meta?.open_url || spotifyUriToOpenUrl(uri) || "").trim();
    window.__veraSpotifyLast = {
      preview_url: preview || "",
      open_url: openUrl,
      title: meta?.title || "",
      artist: meta?.artist || ""
    };
    spotifyUpdateNowState({
      title: meta?.title || "",
      artist: meta?.artist || "",
      paused: false,
      active: true
    });
    const titleEl = document.getElementById(`${prefix}-spotify-track-title`);
    const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);

    const st = await fetch(`${base}/api/spotify/connection-status`, {
      credentials: "include",
      headers: { ...veraSpotifyAuthHeaders() }
    })
      .then((r) => (r.ok ? r.json() : { connected: false }))
      .catch(() => ({ connected: false }));
    const connectedSpotify = !!st.connected;

    if (uri && !window.__veraSpotifyDeviceId && connectedSpotify) {
      await ensureSpotifyWebPlayer(prefix);
      await waitForSpotifyDeviceId(22000);
    }

    if (uri && window.__veraSpotifyDeviceId) {
      if (String(uri).trim().startsWith("spotify:track:")) {
        spotifySetPendingSdkTrack(uri);
      }
      const res = await fetch(`${base}/api/spotify/player/play`, {
        method: "POST",
        credentials: "include",
        headers: { "Content-Type": "application/json", ...veraSpotifyAuthHeaders() },
        body: JSON.stringify({ uris: [uri], device_id: window.__veraSpotifyDeviceId })
      });
      if (res.ok) {
        window.__veraSpotifyPlaybackActive = true;
        if (titleEl) titleEl.textContent = meta?.title || "";
        if (artistEl) artistEl.textContent = meta?.artist || "";
        const playBtn = document.getElementById(`${prefix}-spotify-play`);
        if (playBtn && window.__veraSpotifyPlayer) {
          playBtn.textContent = "⏸";
          playBtn.setAttribute("aria-label", "Pause");
        }
        return;
      }
      spotifyClearPendingSdkTrack();
      let detail = "";
      try {
        const j = await res.json();
        detail = typeof j.detail === "string" ? j.detail : "";
      } catch (_) {
        /* ignore */
      }
      console.warn("[Spotify] play failed", res.status, detail);
      if (artistEl) {
        artistEl.textContent =
          detail || "Couldn't start playback in the browser (Spotify Premium + Web Playback required).";
      }
      return;
    }

    if (connectedSpotify && uri) {
      spotifyClearPendingSdkTrack();
      if (artistEl) {
        artistEl.textContent =
          "Connected, but the in-browser player isn't ready. Confirm Spotify Premium and try again.";
      }
      return;
    }

    spotifyClearPendingSdkTrack();
    const audio = document.getElementById(`${prefix}-spotify-preview-audio`);
    if (!audio) return;
    audio.volume = spotifyGetVolume();
    if (preview) {
      audio.src = preview;
      await audio.play().catch(() => {});
      spotifySyncPlayButtonUi(prefix);
      spotifyUpdateNowState({
        title: meta?.title || "",
        artist: meta?.artist || "",
        position_ms: Math.round((audio.currentTime || 0) * 1000),
        duration_ms: Number.isFinite(audio.duration) ? Math.round(audio.duration * 1000) : 0,
        paused: !!audio.paused,
        active: !audio.paused
      });
      spotifyApplyNowStateToPanel(prefix);
      if (artistEl) artistEl.textContent = meta?.artist || "";
      return;
    }
    audio.removeAttribute("src");
    if (openUrl && !connectedSpotify) {
      window.open(openUrl, "_blank", "noopener,noreferrer");
      if (artistEl) {
        artistEl.textContent =
          `${meta?.artist || ""} — Opened Spotify in a new tab (connect Spotify in this panel for in-page playback).`.trim();
      }
      return;
    }
    if (artistEl) {
      artistEl.textContent =
        "Connect Spotify (Premium) above, or pick a track with a preview / open link.";
    }
  },
  async playPlaylist(playlistUri, meta = {}) {
    const prefix = appModePrefix();
    const base = localBackendBase();
    const contextUri = String(playlistUri || "").trim();
    if (!contextUri) return;
    spotifyClearPendingSdkTrack();

    const st = await fetch(`${base}/api/spotify/connection-status`, {
      credentials: "include",
      headers: { ...veraSpotifyAuthHeaders() }
    })
      .then((r) => (r.ok ? r.json() : { connected: false }))
      .catch(() => ({ connected: false }));
    const connectedSpotify = !!st.connected;
    if (!connectedSpotify) {
      const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
      if (artistEl) artistEl.textContent = "Connect Spotify to play playlists, albums, or artists in VERA.";
      return;
    }
    if (!window.__veraSpotifyDeviceId) {
      await ensureSpotifyWebPlayer(prefix);
      await waitForSpotifyDeviceId(22000);
    }
    if (!window.__veraSpotifyDeviceId) {
      const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
      if (artistEl) artistEl.textContent = "Spotify player not ready. Try again.";
      return;
    }

    const res = await fetch(`${base}/api/spotify/player/play-context`, {
      method: "POST",
      credentials: "include",
      headers: { "Content-Type": "application/json", ...veraSpotifyAuthHeaders() },
      body: JSON.stringify({
        context_uri: contextUri,
        device_id: window.__veraSpotifyDeviceId
      })
    });
    if (!res.ok) {
      let detail = "";
      try {
        const j = await res.json();
        detail = typeof j.detail === "string" ? j.detail : "";
      } catch (_) {
        /* ignore */
      }
      const artistEl = document.getElementById(`${prefix}-spotify-track-artist`);
      if (artistEl) artistEl.textContent = detail || "Couldn't start playback.";
      return;
    }
    let defaultSub = "Playing from playlist";
    if (contextUri.startsWith("spotify:album:")) defaultSub = "Album";
    else if (contextUri.startsWith("spotify:artist:")) defaultSub = "Artist";
    spotifyUpdateNowState({
      title: meta?.playlist_name || "Playlist",
      artist: meta?.context_subtitle || defaultSub,
      paused: false,
      active: true
    });
    spotifyApplyNowStateToPanel(prefix);
  },
  async playPlaylistTrack(playlistUri, trackUri, meta = {}) {
    const prefix = appModePrefix();
    const base = localBackendBase();
    const contextUri = String(playlistUri || "").trim();
    const offsetUri = String(trackUri || "").trim();
    if (!contextUri || !offsetUri) return;

    const st = await fetch(`${base}/api/spotify/connection-status`, {
      credentials: "include",
      headers: { ...veraSpotifyAuthHeaders() }
    })
      .then((r) => (r.ok ? r.json() : { connected: false }))
      .catch(() => ({ connected: false }));
    const connectedSpotify = !!st.connected;
    if (!connectedSpotify) {
      await this.playTrack(offsetUri, meta);
      return;
    }
    if (!window.__veraSpotifyDeviceId) {
      await ensureSpotifyWebPlayer(prefix);
      await waitForSpotifyDeviceId(22000);
    }
    if (!window.__veraSpotifyDeviceId) {
      await this.playTrack(offsetUri, meta);
      return;
    }

    if (String(offsetUri).trim().startsWith("spotify:track:")) {
      spotifySetPendingSdkTrack(offsetUri);
    }
    const res = await fetch(`${base}/api/spotify/player/play-context`, {
      method: "POST",
      credentials: "include",
      headers: { "Content-Type": "application/json", ...veraSpotifyAuthHeaders() },
      body: JSON.stringify({
        context_uri: contextUri,
        offset_uri: offsetUri,
        device_id: window.__veraSpotifyDeviceId
      })
    });
    if (!res.ok) {
      await this.playTrack(offsetUri, meta);
      return;
    }
    spotifyUpdateNowState({
      title: meta?.title || "",
      artist: meta?.artist || "",
      paused: false,
      active: true
    });
    spotifyApplyNowStateToPanel(prefix);
  },
  async togglePlayback() {
    const web = window.__veraSpotifyPlayer;
    if (web) {
      await web.togglePlay();
      return;
    }
    const prefix = appModePrefix();
    const audio = document.getElementById(`${prefix}-spotify-preview-audio`);
    const last = window.__veraSpotifyLast || {};
    if (last.preview_url && audio) {
      if (audio.paused) await audio.play().catch(() => {});
      else audio.pause();
      spotifySyncPlayButtonUi(prefix);
      return;
    }
    if (last.open_url) {
      try {
        if (veraSpotifyGetStoredBearer()) return;
      } catch (_) {
        /* ignore */
      }
      window.open(last.open_url, "_blank", "noopener,noreferrer");
    }
  },
  async seekTo(positionMs) {
    const ms = Math.max(0, Math.floor(Number(positionMs) || 0));
    const prefix = appModePrefix();
    const web = window.__veraSpotifyPlayer;
    if (web) {
      await web.seek(ms);
      spotifyUpdateNowState({ position_ms: ms });
      window.__veraSpotifyResumeWeb = {
        ...(window.__veraSpotifyResumeWeb || {}),
        position_ms: ms
      };
      spotifyApplyNowStateToPanel(prefix);
      return;
    }
    const audio = document.getElementById(`${prefix}-spotify-preview-audio`);
    if (audio) {
      const sec = ms / 1000;
      audio.currentTime = Number.isFinite(sec) ? sec : 0;
      spotifyUpdateNowState({ position_ms: Math.round((audio.currentTime || 0) * 1000) });
      persistSpotifyResumePreview(prefix);
      spotifyApplyNowStateToPanel(prefix);
    }
  },
  async setVolume(volume01) {
    const v = Math.max(0, Math.min(SPOTIFY_VOLUME_MAX, Number(volume01) || 0));
    window.__veraSpotifyVolume = v;
    const prefix = appModePrefix();
    const web = window.__veraSpotifyPlayer;
    if (web && typeof web.setVolume === "function") {
      await web.setVolume(v);
    }
    const audio = document.getElementById(`${prefix}-spotify-preview-audio`);
    if (audio) audio.volume = v;
    const slider = document.getElementById(`${prefix}-spotify-volume`);
    if (slider && document.activeElement !== slider) {
      slider.value = String(Math.round(v * 100));
    }
  },
  getVolume() {
    return spotifyGetVolume();
  },
  async pausePlayback() {
    const prefix = appModePrefix();
    const web = window.__veraSpotifyPlayer;
    if (web && typeof web.pause === "function") {
      await web.pause();
      spotifyUpdateNowState({ paused: true, active: false });
      spotifyApplyNowStateToPanel(prefix);
      return;
    }
    const audio = document.getElementById(`${prefix}-spotify-preview-audio`);
    if (audio) {
      audio.pause();
      spotifySyncPlayButtonUi(prefix);
      spotifyUpdateNowState({
        position_ms: Math.round((audio.currentTime || 0) * 1000),
        duration_ms: Number.isFinite(audio.duration) ? Math.round(audio.duration * 1000) : 0,
        paused: true,
        active: false
      });
      spotifyApplyNowStateToPanel(prefix);
    }
  },
  async resumePlayback() {
    const prefix = appModePrefix();
    const web = window.__veraSpotifyPlayer;
    if (web) {
      if (typeof web.resume === "function") {
        await web.resume();
      } else if (typeof web.togglePlay === "function") {
        await web.togglePlay();
      }
      spotifyUpdateNowState({ paused: false, active: true });
      spotifyApplyNowStateToPanel(prefix);
      return;
    }
    const audio = document.getElementById(`${prefix}-spotify-preview-audio`);
    const last = window.__veraSpotifyLast || {};
    if (audio && last.preview_url && !audio.src) {
      audio.src = last.preview_url;
    }
    if (audio && audio.paused && (audio.src || last.preview_url)) {
      await audio.play().catch(() => {});
      spotifySyncPlayButtonUi(prefix);
      spotifyUpdateNowState({
        position_ms: Math.round((audio.currentTime || 0) * 1000),
        duration_ms: Number.isFinite(audio.duration) ? Math.round(audio.duration * 1000) : 0,
        paused: false,
        active: true
      });
      spotifyApplyNowStateToPanel(prefix);
    }
  }
};