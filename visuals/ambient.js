(function ambientAudioModule() {
  "use strict";

  const STORAGE_KEY = "shengmeng.visual-lab.ambient-enabled";
  const AudioContextClass = window.AudioContext || window.webkitAudioContext;
  const chinese = (document.documentElement.lang || "").toLowerCase().startsWith("zh");
  const copy = chinese
    ? {
        on: "关闭音乐",
        off: "开启音乐",
        resume: "继续音乐",
        unavailable: "音乐不可用",
        statusOn: "背景音乐已开启",
        statusOff: "背景音乐已关闭",
        statusHidden: "页面已隐藏，背景音乐已暂停",
        statusError: "此浏览器无法播放背景音乐"
      }
    : {
        on: "Sound off",
        off: "Sound on",
        resume: "Resume sound",
        unavailable: "Sound unavailable",
        statusOn: "Ambient sound is on",
        statusOff: "Ambient sound is off",
        statusHidden: "Ambient sound paused while the page is hidden",
        statusError: "Ambient sound is unavailable in this browser"
      };

  let root = null;
  let button = null;
  let label = null;
  let status = null;
  let context = null;
  let master = null;
  let voiceBus = null;
  let scheduler = 0;
  let suspendTimer = 0;
  let toneIndex = 0;
  let engineStarted = false;
  let active = false;
  let userActivated = false;
  let destroyed = false;

  function readPreference() {
    try {
      return window.localStorage.getItem(STORAGE_KEY) === "true";
    } catch (_error) {
      return false;
    }
  }

  function writePreference(value) {
    try {
      window.localStorage.setItem(STORAGE_KEY, String(value));
    } catch (_error) {
      // Storage can be unavailable in private or restricted browsing modes.
    }
  }

  let preferred = readPreference();

  function announce(message) {
    if (!status) return;
    status.textContent = "";
    window.requestAnimationFrame(function updateAnnouncement() {
      if (status) status.textContent = message;
    });
  }

  function updateControl(state) {
    if (!root || !button || !label) return;
    root.dataset.state = state;

    if (state === "unsupported") {
      button.disabled = true;
      button.setAttribute("aria-disabled", "true");
      button.setAttribute("aria-pressed", "false");
      button.setAttribute("aria-label", copy.unavailable);
      button.title = copy.unavailable;
      label.textContent = copy.unavailable;
      return;
    }

    const isOn = state === "on";
    const nextLabel = isOn ? copy.on : preferred ? copy.resume : copy.off;
    button.disabled = false;
    button.removeAttribute("aria-disabled");
    button.setAttribute("aria-pressed", String(isOn));
    button.setAttribute("aria-label", nextLabel);
    button.title = nextLabel;
    label.textContent = nextLabel;
  }

  function makeImpulse(audioContext) {
    const duration = 2.8;
    const length = Math.floor(audioContext.sampleRate * duration);
    const impulse = audioContext.createBuffer(2, length, audioContext.sampleRate);

    for (let channel = 0; channel < impulse.numberOfChannels; channel += 1) {
      const data = impulse.getChannelData(channel);
      for (let index = 0; index < length; index += 1) {
        const decay = Math.pow(1 - index / length, 3.4);
        data[index] = (Math.random() * 2 - 1) * decay * 0.34;
      }
    }

    return impulse;
  }

  function createGraph() {
    context = new AudioContextClass({ latencyHint: "playback" });
    const compressor = context.createDynamicsCompressor();
    const dry = context.createGain();
    const wet = context.createGain();
    const reverb = context.createConvolver();

    master = context.createGain();
    voiceBus = context.createGain();
    master.gain.value = 0.0001;
    voiceBus.gain.value = 0.72;
    dry.gain.value = 0.68;
    wet.gain.value = 0.24;
    reverb.buffer = makeImpulse(context);
    compressor.threshold.value = -30;
    compressor.knee.value = 18;
    compressor.ratio.value = 3;
    compressor.attack.value = 0.08;
    compressor.release.value = 0.8;

    voiceBus.connect(dry);
    voiceBus.connect(reverb);
    reverb.connect(wet);
    dry.connect(master);
    wet.connect(master);
    master.connect(compressor);
    compressor.connect(context.destination);
  }

  function addDrone(frequency, level, detune, modulationRate) {
    const oscillator = context.createOscillator();
    const gain = context.createGain();
    const lowpass = context.createBiquadFilter();
    const lfo = context.createOscillator();
    const lfoDepth = context.createGain();
    const now = context.currentTime;

    oscillator.type = "sine";
    oscillator.frequency.value = frequency;
    oscillator.detune.value = detune;
    gain.gain.value = level;
    lowpass.type = "lowpass";
    lowpass.frequency.value = 680;
    lowpass.Q.value = 0.45;
    lfo.type = "sine";
    lfo.frequency.value = modulationRate;
    lfoDepth.gain.value = level * 0.3;

    lfo.connect(lfoDepth);
    lfoDepth.connect(gain.gain);
    oscillator.connect(gain);
    gain.connect(lowpass);
    lowpass.connect(voiceBus);
    oscillator.start(now);
    lfo.start(now);
  }

  function scheduleTone() {
    if (!context || context.state !== "running" || !active || document.hidden) return;

    // D pentatonic frequencies, traversed by fifths for a slow mathematical orbit.
    const scale = [146.83, 164.81, 220, 246.94, 293.66, 329.63, 440];
    toneIndex = (toneIndex + 3) % scale.length;
    const frequency = scale[toneIndex];
    const now = context.currentTime + 0.04;
    const duration = 5.6;
    const oscillator = context.createOscillator();
    const gain = context.createGain();
    const filter = context.createBiquadFilter();

    oscillator.type = toneIndex % 2 ? "sine" : "triangle";
    oscillator.frequency.setValueAtTime(frequency, now);
    oscillator.detune.setValueAtTime(toneIndex % 3 === 0 ? -4 : 3, now);
    filter.type = "lowpass";
    filter.frequency.setValueAtTime(1050 + toneIndex * 95, now);
    filter.Q.value = 0.7;
    gain.gain.setValueAtTime(0.0001, now);
    gain.gain.exponentialRampToValueAtTime(0.027, now + 1.35);
    gain.gain.exponentialRampToValueAtTime(0.0001, now + duration);

    oscillator.connect(filter);
    filter.connect(gain);
    gain.connect(voiceBus);
    oscillator.start(now);
    oscillator.stop(now + duration + 0.08);
    oscillator.addEventListener("ended", function cleanVoice() {
      oscillator.disconnect();
      filter.disconnect();
      gain.disconnect();
    }, { once: true });
  }

  function startEngine() {
    if (engineStarted) return;
    addDrone(73.42, 0.024, -5, 0.061);
    addDrone(110, 0.017, 4, 0.047);
    addDrone(146.83, 0.011, -2, 0.037);
    engineStarted = true;
  }

  function startScheduler() {
    if (scheduler) return;
    scheduleTone();
    scheduler = window.setInterval(scheduleTone, 3400);
  }

  function stopScheduler() {
    if (!scheduler) return;
    window.clearInterval(scheduler);
    scheduler = 0;
  }

  function cancelSuspend() {
    if (!suspendTimer) return;
    window.clearTimeout(suspendTimer);
    suspendTimer = 0;
  }

  function fadeTo(value, duration) {
    if (!context || !master) return;
    const now = context.currentTime;
    const current = Math.max(master.gain.value, 0.0001);
    master.gain.cancelScheduledValues(now);
    master.gain.setValueAtTime(current, now);
    master.gain.exponentialRampToValueAtTime(Math.max(value, 0.0001), now + duration);
  }

  function suspendAfterFade(delay) {
    cancelSuspend();
    suspendTimer = window.setTimeout(function suspendAudio() {
      suspendTimer = 0;
      if (context && context.state === "running") context.suspend().catch(function ignore() {});
    }, delay);
  }

  async function start() {
    if (destroyed || !AudioContextClass) {
      updateControl("unsupported");
      announce(copy.statusError);
      return false;
    }

    try {
      cancelSuspend();
      if (!context) createGraph();
      await context.resume();
      startEngine();
      active = true;
      userActivated = true;
      preferred = true;
      writePreference(true);
      startScheduler();
      fadeTo(0.034, 1.8);
      updateControl("on");
      announce(copy.statusOn);
      return true;
    } catch (_error) {
      active = false;
      updateControl("unsupported");
      announce(copy.statusError);
      return false;
    }
  }

  function stop(options) {
    const settings = options || {};
    active = false;
    stopScheduler();
    fadeTo(0.0001, 0.65);
    suspendAfterFade(760);

    if (!settings.keepPreference) {
      preferred = false;
      writePreference(false);
    }

    updateControl("off");
    if (!settings.silent) announce(copy.statusOff);
  }

  function toggle() {
    if (active) stop();
    else start();
  }

  function handleVisibility() {
    if (!active || !context) return;

    if (document.hidden) {
      stopScheduler();
      fadeTo(0.0001, 0.45);
      suspendAfterFade(560);
      updateControl("hidden");
      announce(copy.statusHidden);
      return;
    }

    if (!userActivated) return;
    cancelSuspend();
    context.resume().then(function restoreAudio() {
      if (!active) return;
      startScheduler();
      fadeTo(0.034, 1.1);
      updateControl("on");
    }).catch(function keepSilent() {
      updateControl("off");
    });
  }

  function mount(options) {
    if (root || destroyed) return root;
    const settings = options || {};
    const parent = settings.parent || document.body;
    const identifier = "ambientAudioStatus-" + Math.random().toString(36).slice(2, 8);

    root = document.createElement("div");
    root.className = "ambient-audio";
    root.dataset.state = "off";
    root.innerHTML = [
      '<button class="ambient-audio__button" type="button" aria-pressed="false" aria-describedby="' + identifier + '">',
      '<span class="ambient-audio__icon" aria-hidden="true"><i></i><i></i><i></i></span>',
      '<span class="ambient-audio__label"></span>',
      "</button>",
      '<span class="ambient-audio__status" id="' + identifier + '" aria-live="polite"></span>'
    ].join("");
    parent.appendChild(root);

    button = root.querySelector(".ambient-audio__button");
    label = root.querySelector(".ambient-audio__label");
    status = root.querySelector(".ambient-audio__status");
    button.addEventListener("click", toggle);
    document.addEventListener("visibilitychange", handleVisibility);

    if (!AudioContextClass) updateControl("unsupported");
    else updateControl("off");
    return root;
  }

  async function destroy() {
    if (destroyed) return;
    destroyed = true;
    active = false;
    stopScheduler();
    cancelSuspend();
    document.removeEventListener("visibilitychange", handleVisibility);
    if (button) button.removeEventListener("click", toggle);
    if (context && context.state !== "closed") {
      try { await context.close(); } catch (_error) { /* Already closed. */ }
    }
    if (root) root.remove();
    root = button = label = status = context = master = voiceBus = null;
  }

  function getState() {
    return {
      supported: Boolean(AudioContextClass),
      mounted: Boolean(root),
      active: active,
      preferred: preferred,
      contextState: context ? context.state : "uninitialized"
    };
  }

  window.VisualLabAmbient = Object.freeze({
    mount: mount,
    start: start,
    stop: stop,
    toggle: toggle,
    destroy: destroy,
    getState: getState
  });

  const script = document.currentScript;
  const autoMount = !script || script.dataset.autoMount !== "false";
  if (autoMount) {
    if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", function () { mount(); }, { once: true });
    else mount();
  }
}());
