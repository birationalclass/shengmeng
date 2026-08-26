(function ambientAudioModule() {
  "use strict";

  const script = document.currentScript;
  const AudioClass = window.Audio;
  const chinese = (document.documentElement.lang || "").toLowerCase().startsWith("zh");
  const copy = chinese
    ? {
        on: "关闭音乐",
        off: "开启音乐",
        blocked: "自动播放受限 · 点击开启音乐",
        loading: "正在加载音乐",
        unavailable: "音乐不可用",
        statusOn: "背景音乐已开启",
        statusOff: "背景音乐已关闭",
        statusBlocked: "浏览器阻止了自动播放，请点击音乐按钮开启",
        statusHidden: "页面已隐藏，背景音乐已暂停",
        statusError: "背景音乐文件无法播放"
      }
    : {
        on: "Sound off",
        off: "Sound on",
        blocked: "Autoplay blocked · Click for sound",
        loading: "Loading sound",
        unavailable: "Sound unavailable",
        statusOn: "Background music is on",
        statusOff: "Background music is off",
        statusBlocked: "Autoplay was blocked. Activate the sound button to begin",
        statusHidden: "Background music paused while the page is hidden",
        statusError: "The background music file could not be played"
      };

  function clampVolume(value) {
    const parsed = Number.parseFloat(value);
    return Number.isFinite(parsed) ? Math.min(1, Math.max(0, parsed)) : 0.45;
  }

  function resolveTrack() {
    const configured = script && script.dataset.track;
    if (configured) return new URL(configured, document.baseURI).href;
    if (script && script.src) return new URL("chaos/curve1.mp3", new URL(".", script.src)).href;
    return new URL("visuals/chaos/curve1.mp3", document.baseURI).href;
  }

  const trackUrl = resolveTrack();
  const volume = clampVolume(script && script.dataset.volume);
  let root = null;
  let button = null;
  let label = null;
  let status = null;
  let audio = null;
  let active = false;
  let blocked = false;
  let startPending = false;
  let playAttemptId = 0;
  let autoStartWanted = true;
  let resumeAfterVisibility = false;
  let firstGestureInstalled = false;
  let destroyed = false;

  function announce(message) {
    if (!status) return;
    status.textContent = "";
    window.requestAnimationFrame(function updateAnnouncement() {
      if (status) status.textContent = message;
    });
  }

  function updateControl(state) {
    if (!root || !button || !label) return;
    root.dataset.state = state === "blocked" ? "off" : state;
    root.dataset.reason = state;

    if (state === "unsupported" || state === "error") {
      button.disabled = true;
      button.setAttribute("aria-disabled", "true");
      button.setAttribute("aria-pressed", "false");
      button.setAttribute("aria-label", copy.unavailable);
      button.title = copy.unavailable;
      label.textContent = copy.unavailable;
      return;
    }

    const isOn = state === "on";
    const nextLabel = isOn
      ? copy.on
      : state === "blocked"
        ? copy.blocked
        : state === "loading"
          ? copy.loading
          : copy.off;
    button.disabled = false;
    button.removeAttribute("aria-disabled");
    button.setAttribute("aria-pressed", String(isOn));
    button.setAttribute("aria-label", nextLabel);
    button.title = nextLabel;
    label.textContent = nextLabel;
  }

  function createAudio() {
    if (audio || !AudioClass) return audio;
    audio = new AudioClass();
    audio.src = trackUrl;
    audio.preload = "auto";
    audio.autoplay = true;
    audio.loop = true;
    audio.volume = volume;
    audio.hidden = true;
    audio.setAttribute("playsinline", "");
    audio.setAttribute("aria-hidden", "true");
    audio.addEventListener("error", handleAudioError);
    if (root) root.appendChild(audio);
    audio.load();
    return audio;
  }

  function isAutoplayBlock(error) {
    return Boolean(error && (error.name === "NotAllowedError" || error.name === "AbortError"));
  }

  async function start(options) {
    const settings = options || {};
    autoStartWanted = true;
    if (destroyed || !AudioClass) {
      updateControl("unsupported");
      announce(copy.statusError);
      return false;
    }
    if (startPending && !settings.force) return false;
    const attemptId = ++playAttemptId;
    startPending = true;
    updateControl("loading");

    try {
      const player = createAudio();
      player.muted = false;
      // Keep play() in the same call stack when start() was invoked by the
      // first pointer/key gesture. Browsers only grant audible playback while
      // that transient user activation is still available.
      const playAttempt = player.play();
      if (playAttempt && typeof playAttempt.then === "function") await playAttempt;
      if (destroyed || attemptId !== playAttemptId) return !player.paused;
      active = !player.paused;
      blocked = false;
      resumeAfterVisibility = false;
      removeFirstGestureRecovery();
      updateControl(active ? "on" : "blocked");
      if (active && !settings.silent) announce(copy.statusOn);
      return active;
    } catch (error) {
      if (destroyed || attemptId !== playAttemptId) return false;
      active = false;
      if (isAutoplayBlock(error)) {
        blocked = true;
        installFirstGestureRecovery();
        updateControl("blocked");
        if (!settings.silent) announce(copy.statusBlocked);
      } else {
        blocked = false;
        updateControl("error");
        announce(copy.statusError);
      }
      return false;
    } finally {
      if (attemptId === playAttemptId) startPending = false;
    }
  }

  function stop(options) {
    const settings = options || {};
    autoStartWanted = false;
    playAttemptId += 1;
    startPending = false;
    active = false;
    blocked = false;
    resumeAfterVisibility = false;
    removeFirstGestureRecovery();
    if (audio) {
      audio.pause();
      if (settings.reset !== false) {
        try { audio.currentTime = 0; } catch (_error) { /* Metadata may not be ready yet. */ }
      }
    }
    updateControl("off");
    if (!settings.silent) announce(copy.statusOff);
  }

  function toggle() {
    if (active || (audio && !audio.paused)) stop();
    else {
      autoStartWanted = true;
      installFirstGestureRecovery();
      start({ force: true });
    }
  }

  function removeFirstGestureRecovery() {
    if (!firstGestureInstalled) return;
    firstGestureInstalled = false;
    document.removeEventListener("pointerdown", handleFirstGesture, true);
    document.removeEventListener("click", handleFirstGesture, true);
    document.removeEventListener("touchend", handleFirstGesture, true);
    document.removeEventListener("keydown", handleFirstGesture, true);
  }

  function installFirstGestureRecovery() {
    if (firstGestureInstalled || destroyed) return;
    firstGestureInstalled = true;
    document.addEventListener("pointerdown", handleFirstGesture, true);
    document.addEventListener("click", handleFirstGesture, true);
    document.addEventListener("touchend", handleFirstGesture, true);
    document.addEventListener("keydown", handleFirstGesture, true);
  }

  function handleFirstGesture(event) {
    if (!autoStartWanted || active || destroyed) {
      removeFirstGestureRecovery();
      return;
    }
    if (button && (event.target === button || button.contains(event.target))) return;
    if (event.type === "keydown" && ["tab", "shift", "control", "alt", "meta", "escape", "m"].includes(event.key.toLowerCase())) return;
    removeFirstGestureRecovery();
    start({ silent: true, force: true });
  }

  function handleAudioError() {
    active = false;
    blocked = false;
    updateControl("error");
    announce(copy.statusError);
  }

  function handleVisibility() {
    if (!audio) return;
    if (document.hidden) {
      resumeAfterVisibility = active && !audio.paused;
      if (resumeAfterVisibility) {
        audio.pause();
        active = false;
        root.dataset.state = "hidden";
        root.dataset.reason = "hidden";
        button.setAttribute("aria-pressed", "false");
        button.setAttribute("aria-label", copy.off);
        button.title = copy.off;
        label.textContent = copy.off;
        announce(copy.statusHidden);
      }
      return;
    }
    if (resumeAfterVisibility) {
      resumeAfterVisibility = false;
      start({ silent: true });
    }
  }

  function handleKeyboard(event) {
    if (event.repeat || event.defaultPrevented || event.key.toLowerCase() !== "m") return;
    const target = event.target;
    if (target instanceof HTMLElement && target.closest("input, textarea, select, dialog, [contenteditable='true']")) return;
    event.preventDefault();
    toggle();
  }

  function mount(options) {
    if (root || destroyed) return root;
    const settings = options || {};
    const configuredParent = script && script.dataset.parent
      ? document.querySelector(script.dataset.parent)
      : null;
    const parent = settings.parent || configuredParent || document.body;
    const identifier = "ambientAudioStatus-" + Math.random().toString(36).slice(2, 8);

    root = document.createElement("div");
    root.className = "ambient-audio";
    root.dataset.state = "off";
    root.dataset.reason = "loading";
    root.innerHTML = [
      '<button class="ambient-audio__button" type="button" aria-pressed="false" aria-describedby="' + identifier + '">',
      '<span class="ambient-audio__icon" aria-hidden="true"><i></i><i></i><i></i></span>',
      '<span class="ambient-audio__label"></span>',
      "</button>",
      '<span class="ambient-audio__status" id="' + identifier + '" aria-live="polite"></span>'
    ].join("");
    parent.appendChild(root);
    if (audio && !audio.isConnected) root.appendChild(audio);

    button = root.querySelector(".ambient-audio__button");
    label = root.querySelector(".ambient-audio__label");
    status = root.querySelector(".ambient-audio__status");
    button.addEventListener("click", toggle);
    document.addEventListener("visibilitychange", handleVisibility);
    document.addEventListener("keydown", handleKeyboard);

    if (!AudioClass) {
      updateControl("unsupported");
      announce(copy.statusError);
    } else {
      createAudio();
      // Install recovery before the speculative autoplay attempt. Otherwise a
      // very fast first click can occur while play() is still pending and be
      // lost before its NotAllowedError installs the listeners.
      installFirstGestureRecovery();
      start({ silent: true });
    }
    return root;
  }

  async function destroy() {
    if (destroyed) return;
    destroyed = true;
    active = false;
    blocked = false;
    document.removeEventListener("visibilitychange", handleVisibility);
    document.removeEventListener("keydown", handleKeyboard);
    removeFirstGestureRecovery();
    if (button) button.removeEventListener("click", toggle);
    if (audio) {
      audio.pause();
      audio.removeEventListener("error", handleAudioError);
      audio.removeAttribute("src");
      audio.load();
    }
    if (root) root.remove();
    root = button = label = status = audio = null;
  }

  function getState() {
    return {
      supported: Boolean(AudioClass),
      mounted: Boolean(root),
      active: active,
      blocked: blocked,
      track: trackUrl,
      volume: volume,
      mediaState: audio ? (audio.paused ? "paused" : "playing") : "uninitialized"
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

  const autoMount = !script || script.dataset.autoMount !== "false";
  if (autoMount) {
    if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", function () { mount(); }, { once: true });
    else mount();
  }
}());
