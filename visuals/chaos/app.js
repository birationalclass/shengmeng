(() => {
  "use strict";

  const SYSTEMS = [
    {
      slug: "chen-lee",
      title: "Chen–Lee Attractor",
      equations: ["dx⁄dt = ax − yz", "dy⁄dt = by + xz", "dz⁄dt = cz + xy⁄3"],
      parameters: "a = 5.0,    b = −10.0,    c = −0.38",
      initial: [1, 1, 1],
      dt: 0.003,
      warmup: 2500,
      pointCount: 36000,
      derivative: (x, y, z) => [5 * x - y * z, -10 * y + x * z, -0.38 * z + x * y / 3]
    },
    {
      slug: "lorenz",
      title: "Lorenz Attractor",
      equations: ["dx⁄dt = σ(y − x)", "dy⁄dt = x(ρ − z) − y", "dz⁄dt = xy − βz"],
      parameters: "σ = 10,    ρ = 28,    β = 8⁄3",
      initial: [0.1, 0, 0],
      dt: 0.005,
      warmup: 2000,
      pointCount: 36000,
      derivative: (x, y, z) => [10 * (y - x), x * (28 - z) - y, x * y - (8 / 3) * z]
    },
    {
      slug: "rossler",
      title: "Rössler Attractor",
      equations: ["dx⁄dt = −y − z", "dy⁄dt = x + ay", "dz⁄dt = b + z(x − c)"],
      parameters: "a = 0.2,    b = 0.2,    c = 5.7",
      initial: [0.1, 0, 0],
      dt: 0.01,
      warmup: 3000,
      pointCount: 36000,
      derivative: (x, y, z) => [-y - z, x + 0.2 * y, 0.2 + z * (x - 5.7)]
    },
    {
      slug: "aizawa",
      title: "Aizawa Attractor",
      equations: [
        "dx⁄dt = (z − b)x − dy",
        "dy⁄dt = dx + (z − b)y",
        "dz⁄dt = c + az − z³⁄3 − (x² + y²)(1 + ez) + fzx³"
      ],
      parameters: "a=.95, b=.7, c=.6, d=3.5, e=.25, f=.1",
      initial: [0.1, 0, 0],
      dt: 0.01,
      warmup: 3000,
      pointCount: 36000,
      derivative: (x, y, z) => {
        const radial = x * x + y * y;
        return [
          (z - 0.7) * x - 3.5 * y,
          3.5 * x + (z - 0.7) * y,
          0.6 + 0.95 * z - z ** 3 / 3 - radial * (1 + 0.25 * z) + 0.1 * z * x ** 3
        ];
      }
    },
    {
      slug: "thomas",
      title: "Thomas Attractor",
      equations: ["dx⁄dt = sin(y) − bx", "dy⁄dt = sin(z) − by", "dz⁄dt = sin(x) − bz"],
      parameters: "b = 0.208186",
      initial: [0.1, 0, 0],
      dt: 0.04,
      warmup: 4000,
      pointCount: 36000,
      derivative: (x, y, z) => [
        Math.sin(y) - 0.208186 * x,
        Math.sin(z) - 0.208186 * y,
        Math.sin(x) - 0.208186 * z
      ]
    },
    {
      slug: "halvorsen",
      title: "Halvorsen Attractor",
      equations: [
        "dx⁄dt = −ax − 4y − 4z − y²",
        "dy⁄dt = −ay − 4z − 4x − z²",
        "dz⁄dt = −az − 4x − 4y − x²"
      ],
      parameters: "a = 1.4",
      initial: [1, 0, 0],
      dt: 0.005,
      warmup: 4000,
      pointCount: 36000,
      derivative: (x, y, z) => [
        -1.4 * x - 4 * y - 4 * z - y * y,
        -1.4 * y - 4 * z - 4 * x - z * z,
        -1.4 * z - 4 * x - 4 * y - x * x
      ]
    }
  ];

  const BASE_POINTS_PER_SECOND = 45;
  const FRAME_TIME_CAP = 0.08;
  const numberFormat = new Intl.NumberFormat("en-US");

  const canvas = document.getElementById("attractorCanvas");
  const stage = document.getElementById("stage");
  const introPanel = document.querySelector(".intro-panel");
  const equationPanel = document.querySelector(".equation-panel");
  const signature = document.getElementById("signature");
  const controlPanel = document.querySelector(".control-panel");
  const systemDock = document.querySelector(".system-dock");
  const systemTitle = document.getElementById("systemTitle");
  const systemCounter = document.getElementById("systemCounter");
  const modelSlug = document.getElementById("modelSlug");
  const equations = document.getElementById("equations");
  const parameters = document.getElementById("parameters");
  const integratorStatus = document.getElementById("integratorStatus");
  const stateReadout = document.getElementById("stateReadout");
  const playState = document.getElementById("playState");
  const pauseButton = document.getElementById("pauseButton");
  const pauseLabel = document.getElementById("pauseLabel");
  const pauseIcon = pauseButton.querySelector(".pause-icon");
  const previousButton = document.getElementById("previousButton");
  const nextButton = document.getElementById("nextButton");
  const resetButton = document.getElementById("resetButton");
  const cameraModeButton = document.getElementById("cameraModeButton");
  const fullscreenButton = document.getElementById("fullscreenButton");
  const fullscreenLabel = document.getElementById("fullscreenLabel");
  const speedControl = document.getElementById("speedControl");
  const speedOutput = document.getElementById("speedOutput");
  const systemOptions = [...document.querySelectorAll(".system-option")];
  const gestureHint = document.getElementById("gestureHint");
  const keysButton = document.getElementById("keysButton");
  const keyGuide = document.getElementById("keyGuide");
  const announcer = document.getElementById("announcer");

  if (!window.ChaosExactRenderer || !window.ChaosCameraRig) {
    throw new Error("The exact Chaos renderer and camera must load before app.js.");
  }

  const renderer = new window.ChaosExactRenderer(canvas);
  const camera = new window.ChaosCameraRig();
  const trajectoryCache = new Map();
  const pointers = new Map();

  const state = {
    width: 1,
    height: 1,
    dpr: 1,
    currentIndex: 0,
    trajectory: null,
    position: 0,
    speed: 1,
    paused: false,
    animationSeconds: 0,
    lastTimestamp: null,
    frame: 0,
    overlayVisible: true,
    primaryPointerId: null,
    dragDistance: 0,
    pointerStartedAsPan: false,
    pinchDistance: null,
    immersiveFallback: false,
    chromeTimer: 0
  };

  function rk4Step(system, current) {
    const { derivative, dt } = system;
    const [x, y, z] = current;
    const k1 = derivative(x, y, z);
    const k2 = derivative(x + k1[0] * dt / 2, y + k1[1] * dt / 2, z + k1[2] * dt / 2);
    const k3 = derivative(x + k2[0] * dt / 2, y + k2[1] * dt / 2, z + k2[2] * dt / 2);
    const k4 = derivative(x + k3[0] * dt, y + k3[1] * dt, z + k3[2] * dt);
    return [
      x + dt * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]) / 6,
      y + dt * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]) / 6,
      z + dt * (k1[2] + 2 * k2[2] + 2 * k3[2] + k4[2]) / 6
    ];
  }

  function safeStep(system, current) {
    const next = rk4Step(system, current);
    if (!next.every(Number.isFinite)) {
      throw new Error(`${system.title} became non-finite; restore the bundled parameters.`);
    }
    return next;
  }

  function buildTrajectory(system) {
    if (trajectoryCache.has(system.slug)) return trajectoryCache.get(system.slug);
    let current = system.initial.slice();
    for (let index = 0; index < system.warmup; index += 1) current = safeStep(system, current);

    const points = new Float32Array(system.pointCount * 3);
    for (let index = 0; index < system.pointCount; index += 1) {
      current = safeStep(system, current);
      const offset = index * 3;
      points[offset] = current[0];
      points[offset + 1] = current[1];
      points[offset + 2] = current[2];
    }
    trajectoryCache.set(system.slug, points);
    return points;
  }

  function precomputeTrajectories() {
    for (const system of SYSTEMS) buildTrajectory(system);
  }

  function setTitle(text) {
    systemTitle.textContent = text;
  }

  function updateSystemPanel(system, index) {
    setTitle(system.title);
    systemCounter.textContent = `${String(index + 1).padStart(2, "0")} / ${String(SYSTEMS.length).padStart(2, "0")}`;
    modelSlug.textContent = system.slug.toUpperCase();
    equations.replaceChildren(...system.equations.map((line) => {
      const row = document.createElement("div");
      row.textContent = line;
      return row;
    }));
    parameters.textContent = system.parameters;
    integratorStatus.textContent = `RK4 · Δt ${system.dt} · ${numberFormat.format(system.pointCount)} points · 300 streams`;
    systemOptions.forEach((button, buttonIndex) => {
      const active = buttonIndex === index;
      button.classList.toggle("is-active", active);
      if (active) button.setAttribute("aria-current", "true");
      else button.removeAttribute("aria-current");
    });
  }

  function updatePauseUI() {
    pauseButton.setAttribute("aria-pressed", String(state.paused));
    pauseLabel.textContent = state.paused ? "Continue" : "Pause";
    pauseIcon.textContent = state.paused ? "▶" : "Ⅱ";
    playState.textContent = state.paused ? "PAUSED" : "LIVE";
    stage.classList.toggle("is-paused", state.paused);
  }

  function updateSpeedUI() {
    speedControl.value = String(state.speed);
    speedOutput.value = `${state.speed}×`;
    speedOutput.textContent = `${state.speed}×`;
  }

  function updateCameraModeUI() {
    cameraModeButton.textContent = `Camera · ${camera.mode}`;
    cameraModeButton.dataset.mode = camera.mode;
    cameraModeButton.setAttribute("aria-label", `Camera mode: ${camera.mode.toLowerCase()}. Activate to cycle mode.`);
  }

  function updateOverlayUI() {
    stage.classList.toggle("overlay-hidden", !state.overlayVisible);
    for (const panel of [introPanel, equationPanel, signature]) {
      if (panel) panel.setAttribute("aria-hidden", String(!state.overlayVisible));
    }
  }

  function toggleOverlay() {
    state.overlayVisible = !state.overlayVisible;
    updateOverlayUI();
    announcer.textContent = state.overlayVisible ? "Formula and signature shown." : "Formula and signature hidden.";
  }

  function resetPlaybackAndCamera() {
    state.position = 0;
    state.speed = 1;
    state.paused = false;
    state.animationSeconds = 0;
    state.lastTimestamp = null;
    camera.reset();
    updateSpeedUI();
    updatePauseUI();
    updateCameraModeUI();
  }

  function selectSystem(index, shouldAnnounce = true) {
    const normalizedIndex = (index + SYSTEMS.length) % SYSTEMS.length;
    const system = SYSTEMS[normalizedIndex];
    state.currentIndex = normalizedIndex;
    stage.classList.add("is-loading");
    state.trajectory = buildTrajectory(system);
    renderer.setModel(state.trajectory);
    resetPlaybackAndCamera();
    updateSystemPanel(system, normalizedIndex);
    stage.classList.remove("is-loading");
    history.replaceState(null, "", `${location.pathname}${location.search}#${system.slug}`);
    if (shouldAnnounce) announcer.textContent = `${system.title} loaded.`;
    systemOptions[normalizedIndex].scrollIntoView({ behavior: "smooth", block: "nearest", inline: "center" });
  }

  function resizeRenderer() {
    const bounds = stage.getBoundingClientRect();
    state.width = Math.max(1, bounds.width);
    state.height = Math.max(1, bounds.height);
    state.dpr = Math.min(window.devicePixelRatio || 1, 2);
    renderer.resize(state.width, state.height, state.dpr);
  }

  function formatCoordinate(value) {
    if (Math.abs(value) >= 100) return value.toFixed(0);
    if (Math.abs(value) >= 10) return value.toFixed(1);
    return value.toFixed(2);
  }

  function updateStateReadout() {
    if (!state.trajectory || state.frame % 6 !== 0) return;
    const pointCount = state.trajectory.length / 3;
    const index = Math.floor(state.position % pointCount);
    const offset = index * 3;
    stateReadout.textContent = [
      `x ${formatCoordinate(state.trajectory[offset])}`,
      `y ${formatCoordinate(state.trajectory[offset + 1])}`,
      `z ${formatCoordinate(state.trajectory[offset + 2])}`
    ].join(" · ");
  }

  function drawFrame(timestamp) {
    if (state.lastTimestamp === null) state.lastTimestamp = timestamp;
    const elapsed = Math.min(FRAME_TIME_CAP, Math.max(0, (timestamp - state.lastTimestamp) / 1000));
    state.lastTimestamp = timestamp;
    state.frame += 1;

    if (!state.paused && state.trajectory) {
      const pointCount = state.trajectory.length / 3;
      state.position = (state.position + elapsed * BASE_POINTS_PER_SECOND * state.speed) % pointCount;
      state.animationSeconds += elapsed;
    }

    camera.advanceManualMotion(elapsed);
    if (state.trajectory) {
      const followStream = camera.followStreamAt(state.animationSeconds, renderer.streamCount);
      const sample = renderer.particleSample(state.position, followStream);
      camera.updateFollowTarget(sample.position, sample.direction, elapsed, state.animationSeconds);
      renderer.render(state.position, state.animationSeconds, camera.poseAt(state.animationSeconds));
      updateStateReadout();
    }
    requestAnimationFrame(drawFrame);
  }

  function togglePause(force) {
    state.paused = typeof force === "boolean" ? force : !state.paused;
    updatePauseUI();
    announcer.textContent = state.paused ? "Animation paused." : "Animation playing.";
  }

  function setSpeed(value) {
    state.speed = Math.max(1, Math.min(9, Math.round(Number(value) || 1)));
    state.paused = false;
    updateSpeedUI();
    updatePauseUI();
    announcer.textContent = `Playback speed ${state.speed} times.`;
  }

  function resetAll() {
    resetPlaybackAndCamera();
    announcer.textContent = "Attractor, speed, and camera reset.";
  }

  function cycleCameraMode() {
    camera.cycleMode();
    updateCameraModeUI();
    announcer.textContent = `Camera mode ${camera.mode.toLowerCase()}.`;
  }

  function dismissGestureHint() {
    gestureHint.classList.add("is-dismissed");
  }

  function pointerDistance() {
    const active = [...pointers.values()];
    if (active.length < 2) return null;
    return Math.hypot(active[0].x - active[1].x, active[0].y - active[1].y);
  }

  canvas.addEventListener("pointerdown", (event) => {
    if (event.pointerType === "mouse" && event.button !== 0) return;
    if (typeof canvas.setPointerCapture === "function") canvas.setPointerCapture(event.pointerId);
    const pan = event.pointerType === "mouse" && event.shiftKey;
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY, pan });
    if (state.primaryPointerId === null) {
      state.primaryPointerId = event.pointerId;
      state.dragDistance = 0;
      state.pointerStartedAsPan = pan;
    }
    state.pinchDistance = pointerDistance();
    dismissGestureHint();
  });

  canvas.addEventListener("pointermove", (event) => {
    const previous = pointers.get(event.pointerId);
    if (!previous) return;
    const current = { x: event.clientX, y: event.clientY, pan: previous.pan };
    pointers.set(event.pointerId, current);
    const deltaX = current.x - previous.x;
    const deltaY = current.y - previous.y;
    if (event.pointerId === state.primaryPointerId) state.dragDistance += Math.hypot(deltaX, deltaY);

    if (pointers.size === 1) {
      if (current.pan) camera.pan(deltaX, deltaY);
      else camera.orbit(deltaX, deltaY);
    } else {
      const distance = pointerDistance();
      if (distance && state.pinchDistance) {
        camera.dolly(Math.log(distance / state.pinchDistance) / Math.log(1.1));
      }
      state.dragDistance = Math.max(state.dragDistance, 5);
      state.pinchDistance = distance;
    }
  });

  function releasePointer(event) {
    const wasPrimary = event.pointerId === state.primaryPointerId;
    const wasTap = wasPrimary && pointers.size === 1 && state.dragDistance <= 4 && !state.pointerStartedAsPan;
    pointers.delete(event.pointerId);
    state.pinchDistance = pointerDistance();
    if (event.type !== "lostpointercapture" && typeof canvas.hasPointerCapture === "function" && canvas.hasPointerCapture(event.pointerId)) {
      canvas.releasePointerCapture(event.pointerId);
    }
    if (wasPrimary) {
      state.primaryPointerId = pointers.size ? pointers.keys().next().value : null;
      state.dragDistance = 0;
      state.pointerStartedAsPan = false;
    }
    if (wasTap) toggleOverlay();
  }

  canvas.addEventListener("pointerup", releasePointer);
  canvas.addEventListener("pointercancel", releasePointer);
  canvas.addEventListener("lostpointercapture", releasePointer);
  canvas.addEventListener("wheel", (event) => {
    event.preventDefault();
    const pixels = event.deltaY * (event.deltaMode === WheelEvent.DOM_DELTA_LINE
      ? 16
      : event.deltaMode === WheelEvent.DOM_DELTA_PAGE
        ? state.height
        : 1);
    camera.dolly(-pixels / 100);
    dismissGestureHint();
  }, { passive: false });

  function fullscreenElement() {
    return document.fullscreenElement
      || document.webkitFullscreenElement
      || document.webkitCurrentFullScreenElement
      || null;
  }

  function enterImmersiveFallback() {
    state.immersiveFallback = true;
    stage.classList.add("is-immersive");
    document.body.classList.add("chaos-immersive");
  }

  function exitImmersiveFallback() {
    state.immersiveFallback = false;
    stage.classList.remove("is-immersive");
    document.body.classList.remove("chaos-immersive");
  }

  function fullscreenIsActive() {
    return fullscreenElement() === stage || state.immersiveFallback;
  }

  function clearChromeTimer() {
    if (!state.chromeTimer) return;
    window.clearTimeout(state.chromeTimer);
    state.chromeTimer = 0;
  }

  function scheduleChromeHide() {
    clearChromeTimer();
    if (!fullscreenIsActive()) return;
    state.chromeTimer = window.setTimeout(() => {
      state.chromeTimer = 0;
      stage.classList.add("controls-hidden");
    }, 2400);
  }

  function revealFullscreenChrome(hold = false) {
    stage.classList.remove("controls-hidden");
    clearChromeTimer();
    if (!hold) scheduleChromeHide();
  }

  function updateFullscreenUI() {
    const active = fullscreenIsActive();
    const ambientControl = document.querySelector(".ambient-audio");
    if (ambientControl && ambientControl.parentElement !== stage) stage.appendChild(ambientControl);
    fullscreenButton.setAttribute("aria-pressed", String(active));
    fullscreenLabel.textContent = active ? "Exit full screen" : "Full screen";
    fullscreenButton.title = active
      ? "Exit full screen (Space / F / F11)"
      : "Enter full screen (Space / F / F11)";
    if (active) revealFullscreenChrome();
    else {
      clearChromeTimer();
      stage.classList.remove("controls-hidden");
    }
    requestAnimationFrame(resizeRenderer);
  }

  async function toggleFullscreen() {
    try {
      const ambientState = window.VisualLabAmbient && window.VisualLabAmbient.getState
        ? window.VisualLabAmbient.getState()
        : null;
      if (ambientState && ambientState.blocked && window.VisualLabAmbient.start) {
        window.VisualLabAmbient.start({ silent: true });
      }
      if (fullscreenElement()) {
        if (document.exitFullscreen) await document.exitFullscreen();
        else if (document.webkitExitFullscreen) document.webkitExitFullscreen();
        else if (document.webkitCancelFullScreen) document.webkitCancelFullScreen();
      } else if (state.immersiveFallback) {
        exitImmersiveFallback();
      } else {
        let request = null;
        if (stage.requestFullscreen) request = stage.requestFullscreen();
        else if (stage.webkitRequestFullscreen) request = stage.webkitRequestFullscreen();
        else if (stage.webkitRequestFullScreen) request = stage.webkitRequestFullScreen();
        if (request && typeof request.then === "function") {
          await Promise.race([
            request,
            new Promise((resolve) => window.setTimeout(resolve, 350))
          ]);
        }
        await new Promise((resolve) => requestAnimationFrame(resolve));
        if (fullscreenElement() !== stage) enterImmersiveFallback();
      }
    } catch (_error) {
      if (!fullscreenElement()) enterImmersiveFallback();
    }
    updateFullscreenUI();
  }

  pauseButton.addEventListener("click", () => togglePause());
  previousButton.addEventListener("click", () => selectSystem(state.currentIndex - 1));
  nextButton.addEventListener("click", () => selectSystem(state.currentIndex + 1));
  resetButton.addEventListener("click", resetAll);
  cameraModeButton.addEventListener("click", cycleCameraMode);
  fullscreenButton.addEventListener("click", toggleFullscreen);
  document.addEventListener("fullscreenchange", updateFullscreenUI);
  document.addEventListener("webkitfullscreenchange", updateFullscreenUI);
  speedControl.addEventListener("input", () => setSpeed(speedControl.value));

  stage.addEventListener("pointermove", () => {
    if (fullscreenIsActive()) revealFullscreenChrome();
  }, { passive: true });
  stage.addEventListener("pointerdown", () => {
    if (fullscreenIsActive()) revealFullscreenChrome();
  }, { passive: true, capture: true });

  for (const menu of [controlPanel, systemDock]) {
    if (!menu) continue;
    menu.addEventListener("pointerenter", () => {
      if (fullscreenIsActive()) revealFullscreenChrome(true);
    });
    menu.addEventListener("pointerleave", scheduleChromeHide);
    menu.addEventListener("focusin", () => {
      if (fullscreenIsActive()) revealFullscreenChrome(true);
    });
    menu.addEventListener("focusout", scheduleChromeHide);
  }

  systemOptions.forEach((button) => {
    button.addEventListener("click", () => selectSystem(Number(button.dataset.system)));
  });

  keysButton.addEventListener("click", () => {
    if (typeof keyGuide.showModal === "function") keyGuide.showModal();
    else keyGuide.setAttribute("open", "");
  });

  keyGuide.addEventListener("click", (event) => {
    if (event.target === keyGuide) keyGuide.close();
  });

  window.addEventListener("keydown", (event) => {
    const target = event.target;
    if (target instanceof HTMLElement && target.closest("input, button, dialog, a, textarea, select, [contenteditable='true']")) return;

    if (fullscreenIsActive()) revealFullscreenChrome();

    if (event.key === "ArrowDown") {
      event.preventDefault();
      selectSystem(state.currentIndex + 1);
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      selectSystem(state.currentIndex - 1);
    } else if (/^[1-9]$/.test(event.key)) {
      setSpeed(Number(event.key));
    } else if (event.key.toLowerCase() === "p") {
      event.preventDefault();
      togglePause();
    } else if (event.key.toLowerCase() === "r") {
      resetAll();
    } else if (event.key.toLowerCase() === "c") {
      cycleCameraMode();
    } else if (event.code === "Space" || event.key.toLowerCase() === "f" || event.key === "F11") {
      event.preventDefault();
      toggleFullscreen();
    } else if (event.key === "Escape" && state.immersiveFallback) {
      exitImmersiveFallback();
      updateFullscreenUI();
    }
  });

  document.addEventListener("visibilitychange", () => {
    state.lastTimestamp = null;
  });

  canvas.addEventListener("webglcontextlost", (event) => {
    event.preventDefault();
    announcer.textContent = "The graphics context was interrupted. Reload the page to resume.";
  });

  const resizeObserver = new ResizeObserver(resizeRenderer);
  resizeObserver.observe(stage);

  stage.classList.add("is-loading");
  precomputeTrajectories();
  resizeRenderer();
  updatePauseUI();
  updateSpeedUI();
  updateCameraModeUI();
  updateOverlayUI();
  updateFullscreenUI();

  const requestedSlug = location.hash.replace(/^#/, "");
  const requestedIndex = SYSTEMS.findIndex((system) => system.slug === requestedSlug);
  selectSystem(requestedIndex >= 0 ? requestedIndex : 0, false);
  window.addEventListener("hashchange", () => {
    const slug = location.hash.replace(/^#/, "");
    const index = SYSTEMS.findIndex((system) => system.slug === slug);
    if (index >= 0 && index !== state.currentIndex) selectSystem(index, false);
  });
  requestAnimationFrame(drawFrame);
})();
