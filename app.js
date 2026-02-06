/* =========================
   SESSION SETUP (PERSISTENT)
========================= */

let sessionId = localStorage.getItem("vera_session_id");
if (!sessionId) {
  sessionId = crypto.randomUUID();
  localStorage.setItem("vera_session_id", sessionId);
}

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
let paused = false;
let rafId = null;
let fillerTimer = null;
let fillerPlayedThisTurn = false;
let interruptSpeechFrames = 0;
let pttRecording = false;

let fillerPlaying = false;
let fillerStartedAt = 0;
let pendingMainAnswer = null;
let audioStartedAt = 0;
// let interruptStart = 0;
let listeningMode = "continuous"; 

const FILLER_DELAY_MS = 5300;  // feels natural
const FILLER_GRACE_MS = 1000;  
const pttBtn = document.getElementById("ptt");

const FILLER_AUDIO_FILES = [
  "/static/fillers/moment.wav",
  "/static/fillers/one_second.wav",
  "/static/fillers/give_me_a_second.wav",
  "/static/fillers/one_moment.wav"
];
let requestInFlight = false; // 🔑 NEW

function startFillerTimer() {
  clearTimeout(fillerTimer);

  fillerPlaying = false;
  fillerStartedAt = 0;

  fillerTimer = setTimeout(() => {
    if (!requestInFlight) return;
    if (fillerPlaying) return;
    if (paused) return; 

    const filler =
      FILLER_AUDIO_FILES[Math.floor(Math.random() * FILLER_AUDIO_FILES.length)];

    fillerPlaying = true;
    fillerPlayedThisTurn = true;
    fillerStartedAt = performance.now();

    const fillerSrc = `${API_URL}${filler}`;
    resetAudioHandlers();
    audioEl.src = fillerSrc;
    audioEl.play().catch(console.warn);

    audioEl.addEventListener(
      "ended",
      () => {
        if (audioEl.src !== fillerSrc) return; // 🔑 guard
        fillerPlaying = false;

        if (!requestInFlight && pendingMainAnswer) {
          setTimeout(() => {
            pendingMainAnswer?.();
            pendingMainAnswer = null;
          }, FILLER_GRACE_MS);
        }
      },
      { once: true }
    );
  }, FILLER_DELAY_MS);
}

/* =========================
   CONFIG
========================= */

const VOLUME_THRESHOLD = 0.009; // TUNER
const SILENCE_MS = 950;     // silence before ending speech
const TRAILING_MS = 300;   // guaranteed tail
const MAX_WAIT_FOR_SPEECH_MS = 2000;
const MIN_AUDIO_BYTES = 1500;
const INTERRUPT_MIN_FRAMES = 1; 

const INTERRUPT_ZCR_MIN = 0.015;
const INTERRUPT_ZCR_MAX = 0.25; 
const MAX_SPEECH_RMS = 0.080;
const INTERRUPT_RMS = 0.010;   // higher than normal speech start
// const INTERRUPT_MS = 140;    
const API_URL = "https://vera-api.vera-api-ned.workers.dev";

/* =========================
   DOM
========================= */

const recordBtn = document.getElementById("record");
const statusEl = document.getElementById("status");
const convoEl = document.getElementById("conversation");
const audioEl = document.getElementById("audio");

const serverStatusEl = document.getElementById("server-status");
const serverStatusInlineEl = document.getElementById("server-status-inline");

const feedbackInput = document.getElementById("feedback-input");
const sendFeedbackBtn = document.getElementById("send-feedback");
const feedbackStatusEl = document.getElementById("feedback-status");

const textInput = document.getElementById("text-input");
const sendTextBtn = document.getElementById("send-text");
const IS_MOBILE = window.matchMedia("(max-width: 768px)").matches;

/* =========================
   SERVER HEALTH
========================= */

async function checkServer() {
  let online = false;
  try {
    const res = await fetch(`${API_URL}/health`, { cache: "no-store" });
    online = res.ok;
  } catch {}

  recordBtn.disabled = !online;
  recordBtn.style.opacity = online ? "1" : "0.5";

  if (serverStatusEl) {
    serverStatusEl.textContent = online
      ? "🟢 Server Online"
      : "🔴 Server Offline";
    serverStatusEl.className = `server-status ${online ? "online" : "offline"}`;
  }

  if (serverStatusInlineEl) {
    serverStatusInlineEl.textContent = online ? "🟢 Online" : "🔴 Offline";
    serverStatusInlineEl.className =
      `server-status ${online ? "online" : "offline"} mobile-only`;
  }
}

checkServer();
setInterval(checkServer, 15_000);

/* =========================
   UI HELPERS
========================= */

function setStatus(text, cls) {
  statusEl.textContent = text;
  statusEl.className = `status ${cls}`;
}

function addBubble(text, who) {
  const row = document.createElement("div");
  row.className = `message-row ${who}`;

  const bubble = document.createElement("div");
  bubble.className = `bubble ${who}`;
  bubble.textContent = text;

  row.appendChild(bubble);
  convoEl.appendChild(row);
  convoEl.scrollTop = convoEl.scrollHeight;
}

async function sendCommand(action) {
  const formData = new FormData();
  formData.append("session_id", sessionId);
  formData.append("action", action);

  await fetch(`${API_URL}/command`, {
    method: "POST",
    body: formData
  });
}

async function sendUnpauseCommand() {
  const formData = new FormData();

  // send a tiny silent blob (backend already ignores noise safely)
  const silentBlob = new Blob([new Uint8Array(2000)], { type: "audio/webm" });

  formData.append("audio", silentBlob);
  formData.append("session_id", sessionId);

  await fetch(`${API_URL}/infer`, {
    method: "POST",
    body: formData
  });
}

let fillerAuthInterval = null;

// function waitForFillerAuthorization() {
//   if (fillerAuthInterval) return;

//   fillerAuthInterval = setInterval(async () => {
//     if (!requestInFlight) {
//       clearInterval(fillerAuthInterval);
//       fillerAuthInterval = null;
//       return;
//     }

//     const res = await fetch(
//       `${API_URL}/thinking_allowed?session_id=${sessionId}`,
//       { cache: "no-store" }
//     );
//     const data = await res.json();

//     if (data.allow_filler) {
//       clearInterval(fillerAuthInterval);
//       fillerAuthInterval = null;

//       // 🔑 THIS IS THE ONLY PLACE WE CALL IT
//       startFillerTimer();
//     }
//   }, 150);
// }

function interruptSpeech() {
  if (audioEl.paused || !interruptRecording) return;
  setStatus("Listening… (interrupted)", "recording");
  resetAudioHandlers();

  audioEl.pause();
  audioEl.currentTime = 0;

  clearTimeout(fillerTimer);
  fillerPlaying = false;
  pendingMainAnswer = null;

  listening = true;
  processing = false;
  
  
  interruptLastVoiceTime = performance.now();
  requestAnimationFrame(detectInterruptSpeechEnd);
}

function detectInterrupt() {
  if (!analyser) {
    requestAnimationFrame(detectInterrupt);
    return;
  }

  const buf = new Float32Array(analyser.fftSize);
  analyser.getFloatTimeDomainData(buf);

  // RMS
  let sum = 0;
  for (let i = 0; i < buf.length; i++) sum += buf[i] * buf[i];
  const rms = Math.sqrt(sum / buf.length);

  // ZCR
  const zcr = computeZCR(buf);

  const now = performance.now();

  // Only interrupt while VERA is speaking (not filler)
  if (
  listeningMode === "continuous" &&
  !audioEl.paused &&
  !fillerPlaying 
) {
    // grace period to avoid clicks
    if (now - audioStartedAt > 200) {

      const speechLike =
        rms > INTERRUPT_RMS &&
        rms < MAX_SPEECH_RMS &&
        zcr > INTERRUPT_ZCR_MIN &&
        zcr < INTERRUPT_ZCR_MAX;

      if (speechLike) {
        if (interruptSpeechFrames === 0) {
          interruptSpeechStart = now;
        }
        interruptSpeechFrames++;
      } else {
        interruptSpeechFrames = 0;
        interruptSpeechStart = 0;
      }

      if (
        interruptSpeechFrames >= INTERRUPT_MIN_FRAMES &&
        now - interruptSpeechStart > 120
      ) {
        interruptSpeech();
        interruptSpeechFrames = 0;
        interruptSpeechStart = 0;
      }
    }
  } else {
    interruptSpeechFrames = 0;
  }

  if (Math.random() < 0.02) {
    console.log(
      "rms:",
      rms.toFixed(4),
      "zcr:",
      zcr.toFixed(3),
      "frames:",
      interruptSpeechFrames
    );
  }

  requestAnimationFrame(detectInterrupt);
}

function resetAudioHandlers() {
  audioEl.onplay = null;
  audioEl.onended = null;
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

  if (rms > VOLUME_THRESHOLD) {
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

function startInterruptCapture() {
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
  pendingMainAnswer = null; 
  if (blob.size < MIN_AUDIO_BYTES) {
    listening = true;
    return;
  }

  requestInFlight = true;
  startFillerTimer();
  processing = true;
  fillerPlayedThisTurn = false;
  setStatus("Thinking…", "thinking");

  // ✅ start filler exactly like normal flow

  const formData = new FormData();
  formData.append("audio", blob);
  formData.append("session_id", sessionId);
  formData.append("mode", "interrupt"); // backend can branch if desired

  try {
    const res = await fetch(`${API_URL}/infer`, {
      method: "POST",
      body: formData
    });

    const data = await res.json();

    requestInFlight = false;
    clearTimeout(fillerTimer);
    fillerPlaying = false;

    /* =========================
       CONTROL FLOW (FIRST)
    ========================= */

    if (data.skip) {
      processing = false;
      listening = true;
      startListening();
      return;
    }

    if (listeningMode === "continuous" && data.command === "pause") {
      paused = true;
      processing = false;
      setStatus("Paused — say “unpause” or press mic", "paused");
      listening = true;
      startListening();
      return;
    }

    if (listeningMode === "continuous" && data.command === "unpause") {
      paused = false;
      processing = false;
      setStatus("Listening…", "recording");
      listening = true;
      startListening();
      return;
    }

    if (listeningMode === "continuous" && data.paused) {
      paused = true;
      processing = false;
      setStatus("Paused — say “unpause” or press mic", "paused");
      listening = true;
      startListening();
      return;
    }

    paused = false;

    /* =========================
       NORMAL INTERRUPT REPLY
    ========================= */

    addBubble(data.transcript, "user");

    playInterruptAnswer(data);

  } catch {
    requestInFlight = false;
    clearTimeout(fillerTimer);
    fillerPlaying = false;
    setStatus("Server error", "offline");
    listening = true;
  }
}

function playInterruptAnswer(data) {
  addBubble(data.reply, "vera");
  resetAudioHandlers();
  audioEl.src = `${API_URL}${data.audio_url}`;
  audioEl.play();

  audioEl.onplay = () => {
    audioStartedAt = performance.now();
    setStatus("Speaking… (can only be interrupted once)", "speaking");
    processing = false;
  };

  audioEl.onended = () => {
    listening = true;
    startListening(); 
  };
}
/* =========================
   MIC INIT
========================= */

async function initMic() {
  if (micStream) return;

  micStream = await navigator.mediaDevices.getUserMedia({
    audio: {
      echoCancellation: false,
      noiseSuppression: false,
      autoGainControl: false
    }
  });

  audioCtx = new AudioContext({ sampleRate: 16000 });
  await audioCtx.resume();

  analyser = audioCtx.createAnalyser();
  analyser.fftSize = 2048;

  audioCtx.createMediaStreamSource(micStream).connect(analyser);
  detectInterrupt();

}

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

  if (rms > VOLUME_THRESHOLD) {
    hasSpoken = true;
    lastVoiceTime = now;
  }

  if (
    hasSpoken &&
    now - lastVoiceTime > SILENCE_MS + TRAILING_MS &&
    audioEl.paused // 🔑 only stop when not speaking
  ) {
    mediaRecorder.stop();
    return;
  }

  rafId = requestAnimationFrame(detectSpeech);
}

/* =========================
   START LISTENING
========================= */

function startListening() {
  if (!listening || processing) return;

  audioChunks = [];
  hasSpoken = false;
  lastVoiceTime = 0;

  mediaRecorder = new MediaRecorder(micStream);
  mediaRecorder.ondataavailable = e => audioChunks.push(e.data);
  mediaRecorder.onstop = handleUtterance;

  mediaRecorder.start();
  detectSpeech();

  setTimeout(() => {
    if (!hasSpoken && mediaRecorder.state === "recording") {
      mediaRecorder.stop();
    }
  }, MAX_WAIT_FOR_SPEECH_MS);

  setStatus(
    paused ? "Paused — say “unpause” or press mic" : "Listening…",
    paused ? "paused" : "recording"
  );
}

/* =========================
   HANDLE UTTERANCE
========================= */

async function handleUtterance() {
  if (listeningMode === "continuous" && !hasSpoken) {
    processing = false;
    startListening();
    return;
  }

  const blob = new Blob(audioChunks, { type: "audio/webm" });

  if (blob.size < MIN_AUDIO_BYTES) {
    processing = false;

    if (listeningMode === "continuous") {
      startListening();
    }

    return;
  }
  requestInFlight = true;
  startFillerTimer();
  processing = true;
  fillerPlayedThisTurn = false;
  setStatus("Thinking…", "thinking");


  const formData = new FormData();
  formData.append("audio", blob);
  formData.append("session_id", sessionId);

  // 🔑 ADD THIS
  if (listeningMode === "ptt") {
    formData.append("mode", "ptt");
  }

  try {
    const res = await fetch(`${API_URL}/infer`, {
      method: "POST",
      body: formData
    });

    const data = await res.json();
    requestInFlight = false;
    clearTimeout(fillerTimer);

    // 🔑 HANDLE CONTROL FLOW FIRST (NO AUDIO YET)
    if (data.skip) {
      processing = false;

      if (listeningMode === "continuous") {
        startListening();
      }

      return;
    }

    if (listeningMode === "continuous" && data.command === "pause") {
      paused = true;
      processing = false;
      setStatus("Paused — say “unpause” or press mic", "paused");
      listening = true;
      startListening();
      return;
    }

    if (listeningMode === "continuous" && data.command === "unpause") {
      paused = false;
      processing = false;
      setStatus("Listening…", "recording");
      listening = true;
      startListening();
      return;
    }

    if (listeningMode === "continuous" && data.paused) {
      paused = true;
      processing = false;
      setStatus("Paused — say “unpause” or press mic", "paused");
      listening = true;
      startListening();
      return;
    }

    paused = false;

    addBubble(data.transcript, "user");

    const playMainAnswer = () => {
      if (fillerPlayedThisTurn) {
        setTimeout(() => {
          addBubble(data.reply, "vera");
        }, FILLER_GRACE_MS);
      } else {
        addBubble(data.reply, "vera");
      }
      resetAudioHandlers();
      audioEl.src = `${API_URL}${data.audio_url}`;
      audioEl.play();

      audioEl.onplay = () => {
        audioStartedAt = performance.now();
        setStatus("Speaking… (Interruptible)", "speaking");
        startInterruptCapture();
      };

      audioEl.onended = () => {
        processing = false;

        if (listeningMode === "continuous") {
          startListening();
        }
      };
    };

    if (fillerPlaying) {
      // Store callback until filler ends
      pendingMainAnswer = playMainAnswer;
    } else {
      playMainAnswer();
    }

  } catch {
    processing = false;
    requestInFlight = false;
    clearTimeout(fillerTimer);
    setStatus("Server error", "offline");
  }
}

/* =========================
   TEXT INPUT PIPELINE
========================= */
function micIsReady() {
  return !!micStream;
}

async function sendTextMessage() {
  const text = textInput.value.trim();

  // 🔑 EARLY GUARD — before requestInFlight / thinking
  if (/pause/i.test(text) && !micIsReady()) {
    addBubble(text, "user");
    setStatus("Can’t pause — microphone isn’t active", "idle");

    // HARD RESET
    requestInFlight = false;
    processing = false;
    paused = false;
    listening = false;

    textInput.value = "";
    return;
  }

  // 🔑 recover from offline
  if (statusEl.classList.contains("offline")) {
    requestInFlight = false;
    processing = false;
    paused = false;
    listening = false;
    setStatus("Ready", "idle");
  }

  if (!text || requestInFlight) return;
  textInput.value = "";

  listening = false;
  processing = true;
  requestInFlight = true;
  setStatus("Thinking…", "thinking");
  startFillerTimer();
  clearTimeout(fillerTimer);
  fillerPlaying = false;
  pendingMainAnswer = null;

  addBubble(text, "user");

  try {
    const res = await fetch(`${API_URL}/text`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        text,
        session_id: sessionId
      })
    });

    const data = await res.json();

    requestInFlight = false;

    if (data.command === "pause") {
      processing = false;
      requestInFlight = false;

      if (!micIsReady()) {
        // 🔑 graceful rejection
        setStatus("Can’t pause — microphone isn’t active", "idle");
        paused = false;
        listening = false;
        return;
      }

      paused = true;
      setStatus("Paused — say “unpause” or press mic", "paused");

      listening = true;
      startListening();
      return;
    }

    if (listeningMode === "continuous" && data.command === "unpause") {
      paused = false;
      processing = false;

      setStatus("Listening…", "recording");

      listening = true;
      startListening();
      return;
    }

    if (data.paused) {
      paused = true;
      processing = false;

      setStatus("Paused — say “unpause” or press mic", "paused");

      listening = true;
      startListening();
      return;
    }
    const playReply = () => {
      addBubble(data.reply, "vera");

      if (data.audio_url) {
        audioEl.src = `${API_URL}${data.audio_url}`;
        audioEl.play();
      }

      audioEl.onplay = () => {
        audioStartedAt = performance.now();
        setStatus("Speaking…", "speaking");
      };

      audioEl.onended = () => {
        processing = false;
        listening = true;
        startListening();
      };
    };

    playReply();

  } catch (err) {
    console.error(err);
    requestInFlight = false;
    processing = false;
    setStatus("Server error", "offline");
  }
}

/* =========================
   MIC BUTTON
========================= */
if (pttBtn) {
  pttBtn.onclick = async () => {
    // prevent double firing while request is running
    if (requestInFlight) return;

    // ---------- START PTT ----------
    if (!pttRecording) {
      listeningMode = "ptt";
      pttRecording = true;

      await initMic();

      listening = true;
      processing = false;

      audioChunks = [];
      hasSpoken = false;
      lastVoiceTime = 0;

      mediaRecorder = new MediaRecorder(micStream);
      mediaRecorder.ondataavailable = e => audioChunks.push(e.data);
      mediaRecorder.onstop = handleUtterance;

      mediaRecorder.start();

      setStatus("Listening (PTT)… tap again to send", "recording");
      return;
    }

    // ---------- STOP PTT ----------
    if (pttRecording) {
      pttRecording = false;
      listening = false;

      if (mediaRecorder && mediaRecorder.state === "recording") {
        mediaRecorder.stop(); // triggers handleUtterance()
      }

      setStatus("Processing…", "thinking");
    }
  };
}

recordBtn.onclick = async () => {
  listeningMode = "continuous";   // 🔑 CRITICAL FIX

  if (!listening) {
    await initMic();
    listening = true;
    paused = false;
    startListening();
    return;
  }

  if (paused) {
  paused = false;
  await sendCommand("unpause");
} else {
  paused = true;
  await sendCommand("pause");
}

processing = false;
startListening();
}

if (!IS_MOBILE && sendTextBtn && textInput) {
  sendTextBtn.onclick = sendTextMessage;

  textInput.addEventListener("keydown", (e) => {
    if (e.key === "Enter") {
      sendTextMessage();
    }
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
          session_id: sessionId,
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
