(() => {
  "use strict";

  const SYSTEMS = [
    {
      slug: "chen-lee",
      title: "Chen–Lee Attractor",
      equations: ["dx⁄dt = ax − yz", "dy⁄dt = by + xz", "dz⁄dt = cz + xy⁄3"],
      parameters: "a = 5.0,    b = −10.0,    c = −0.38",
      initial: [1.0, 1.0, 1.0],
      dt: 0.003,
      warmup: 2500,
      pointCount: 36000,
      palette: [[125, 235, 201], [75, 200, 207], [221, 179, 91]],
      derivative: (x, y, z) => [5.0 * x - y * z, -10.0 * y + x * z, -0.38 * z + x * y / 3.0]
    },
    {
      slug: "lorenz",
      title: "Lorenz Attractor",
      equations: ["dx⁄dt = σ(y − x)", "dy⁄dt = x(ρ − z) − y", "dz⁄dt = xy − βz"],
      parameters: "σ = 10,    ρ = 28,    β = 8⁄3",
      initial: [0.1, 0.0, 0.0],
      dt: 0.005,
      warmup: 2000,
      pointCount: 36000,
      palette: [[82, 202, 212], [125, 235, 201], [221, 179, 91]],
      derivative: (x, y, z) => [10.0 * (y - x), x * (28.0 - z) - y, x * y - (8.0 / 3.0) * z]
    },
    {
      slug: "rossler",
      title: "Rössler Attractor",
      equations: ["dx⁄dt = −y − z", "dy⁄dt = x + ay", "dz⁄dt = b + z(x − c)"],
      parameters: "a = 0.2,    b = 0.2,    c = 5.7",
      initial: [0.1, 0.0, 0.0],
      dt: 0.01,
      warmup: 3000,
      pointCount: 36000,
      palette: [[221, 179, 91], [125, 235, 201], [82, 202, 212]],
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
      initial: [0.1, 0.0, 0.0],
      dt: 0.01,
      warmup: 3000,
      pointCount: 36000,
      palette: [[125, 235, 201], [221, 179, 91], [115, 166, 218]],
      derivative: (x, y, z) => {
        const radial = x * x + y * y;
        return [
          (z - 0.7) * x - 3.5 * y,
          3.5 * x + (z - 0.7) * y,
          0.6 + 0.95 * z - z ** 3 / 3.0 - radial * (1.0 + 0.25 * z) + 0.1 * z * x ** 3
        ];
      }
    },
    {
      slug: "thomas",
      title: "Thomas Attractor",
      equations: ["dx⁄dt = sin(y) − bx", "dy⁄dt = sin(z) − by", "dz⁄dt = sin(x) − bz"],
      parameters: "b = 0.208186",
      initial: [0.1, 0.0, 0.0],
      dt: 0.04,
      warmup: 4000,
      pointCount: 36000,
      palette: [[103, 221, 178], [82, 202, 212], [221, 179, 91]],
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
      initial: [1.0, 0.0, 0.0],
      dt: 0.005,
      warmup: 4000,
      pointCount: 36000,
      palette: [[221, 179, 91], [99, 217, 180], [82, 202, 212]],
      derivative: (x, y, z) => [
        -1.4 * x - 4.0 * y - 4.0 * z - y * y,
        -1.4 * y - 4.0 * z - 4.0 * x - z * z,
        -1.4 * z - 4.0 * x - 4.0 * y - x * x
      ]
    }
  ];

  const CAMERA_MODES = ["FREE", "CINEMATIC", "MANUAL"];
  const FREE_CYCLE_SECONDS = 90;
  const CINEMATIC_DURATION_SECONDS = 183;
  const MANUAL_RESPONSE_PER_SECOND = 18;
  const CAMERA_STREAM_COUNT = 5;
  const CINEMATIC_KEYFRAMES = [
    [0,   { yaw: -0.70, pitch: 0.20, zoom: 0.90, target: [0, 0, 0], framing: [0, 0] }],
    [18,  { yaw: -0.36, pitch: 0.46, zoom: 1.02, target: [0, 0, 0], framing: [0, 0] }],
    [42,  { yaw: 0.14, pitch: 1.05, zoom: 1.28, target: [0, 0, 0], framing: [0, 0.12] }],
    [66,  { yaw: 0.62, pitch: 0.88, zoom: 1.10, target: [0, 0, 0], framing: [0, 0] }],
    [94,  { yaw: 1.30, pitch: 0.96, zoom: 1.34, target: [0, 0, 0], framing: [0, 0.10] }],
    [117, { yaw: 1.92, pitch: 0.50, zoom: 1.62, target: [0, 0, 0], framing: [-0.03, 0.02] }],
    [135, { yaw: 2.52, pitch: 0.13, zoom: 2.72, target: [0, 0, 0], framing: [-0.05, -0.02] }],
    [150, { yaw: 3.16, pitch: 0.36, zoom: 1.72, target: [0, 0, 0], framing: [0.02, 0.02] }],
    [169, { yaw: 4.02, pitch: 0.86, zoom: 1.32, target: [3.5 / 30, 0, 0], framing: [0.13, 0.28] }],
    [183, { yaw: 4.70, pitch: 0.38, zoom: 1.05, target: [2 / 30, 0, 0], framing: [0.06, 0.05] }]
  ];

  const canvas = document.getElementById("attractorCanvas");
  const context = canvas.getContext("2d", { alpha: true, desynchronized: true });
  const stage = document.getElementById("stage");
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
  const trailControl = document.getElementById("trailControl");
  const trailOutput = document.getElementById("trailOutput");
  const systemOptions = [...document.querySelectorAll(".system-option")];
  const gestureHint = document.getElementById("gestureHint");
  const keysButton = document.getElementById("keysButton");
  const keyGuide = document.getElementById("keyGuide");
  const announcer = document.getElementById("announcer");
  const reducedMotionQuery = window.matchMedia("(prefers-reduced-motion: reduce)");

  const trajectoryCache = new Map();
  const pointers = new Map();
  const stars = createStars(180);
  const numberFormat = new Intl.NumberFormat("en-US");

  const state = {
    width: 1,
    height: 1,
    dpr: 1,
    currentIndex: 0,
    trajectory: null,
    position: 0,
    speed: 1,
    trailLength: 4200,
    paused: reducedMotionQuery.matches,
    cameraMode: "FREE",
    cameraSeconds: 0,
    yawOffset: 0,
    pitchOffset: 0,
    zoomMultiplier: 1,
    targetOffset: [0, 0, 0],
    desiredYawOffset: 0,
    desiredPitchOffset: 0,
    desiredZoomMultiplier: 1,
    desiredTargetOffset: [0, 0, 0],
    trackedTarget: [0, 0, 0],
    trackedVelocity: [0, 0, 0],
    hasTrackingTarget: false,
    trackedFollowYaw: 0,
    followYawCycle: -1,
    lastTimestamp: null,
    frame: 0,
    pinchDistance: null,
    loadSequence: 0
  };

  function createStars(count) {
    let seed = 0x2f6e2b1;
    const random = () => {
      seed = (1664525 * seed + 1013904223) >>> 0;
      return seed / 4294967296;
    };
    return Array.from({ length: count }, () => ({
      x: random(),
      y: random(),
      size: 0.25 + random() * 0.9,
      alpha: 0.08 + random() * 0.32,
      gold: random() > 0.91
    }));
  }

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

  function buildTrajectory(system) {
    if (trajectoryCache.has(system.slug)) return trajectoryCache.get(system.slug);

    let current = system.initial.slice();
    for (let index = 0; index < system.warmup; index += 1) current = rk4Step(system, current);

    const points = new Float32Array(system.pointCount * 3);
    let meanX = 0;
    let meanY = 0;
    let meanZ = 0;

    for (let index = 0; index < system.pointCount; index += 1) {
      current = rk4Step(system, current);
      if (!current.every(Number.isFinite)) throw new Error(`${system.title} produced a non-finite state.`);
      const offset = index * 3;
      points[offset] = current[0];
      points[offset + 1] = current[1];
      points[offset + 2] = current[2];
      meanX += current[0];
      meanY += current[1];
      meanZ += current[2];
    }

    meanX /= system.pointCount;
    meanY /= system.pointCount;
    meanZ /= system.pointCount;

    const stride = Math.max(1, Math.floor(system.pointCount / 2400));
    const sampledRadii = [];
    for (let index = 0; index < system.pointCount; index += stride) {
      const offset = index * 3;
      const dx = points[offset] - meanX;
      const dy = points[offset + 1] - meanY;
      const dz = points[offset + 2] - meanZ;
      sampledRadii.push(Math.hypot(dx, dy, dz));
    }
    sampledRadii.sort((left, right) => left - right);
    const radius = sampledRadii[Math.floor((sampledRadii.length - 1) * 0.98)] || 1;

    for (let offset = 0; offset < points.length; offset += 3) {
      points[offset] = (points[offset] - meanX) / radius;
      points[offset + 1] = (points[offset + 1] - meanY) / radius;
      points[offset + 2] = (points[offset + 2] - meanZ) / radius;
    }

    const trajectory = { points, center: [meanX, meanY, meanZ], radius, count: system.pointCount };
    trajectoryCache.set(system.slug, trajectory);
    return trajectory;
  }

  function setTitle(text) {
    const splitAt = text.lastIndexOf(" ");
    systemTitle.replaceChildren(
      document.createTextNode(text.slice(0, splitAt)),
      document.createElement("br"),
      document.createTextNode(text.slice(splitAt + 1))
    );
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
    integratorStatus.textContent = `RK4 · Δt ${system.dt} · ${numberFormat.format(system.pointCount)} points`;
    systemOptions.forEach((button, buttonIndex) => {
      const isActive = buttonIndex === index;
      button.classList.toggle("is-active", isActive);
      if (isActive) button.setAttribute("aria-current", "true");
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

  function updateCameraModeUI() {
    cameraModeButton.textContent = `Camera · ${state.cameraMode}`;
    cameraModeButton.dataset.mode = state.cameraMode;
    cameraModeButton.setAttribute("aria-label", `Camera mode: ${state.cameraMode.toLowerCase()}. Activate to cycle mode.`);
  }

  function resetCamera(resetClock = true) {
    state.cameraMode = "FREE";
    if (resetClock) state.cameraSeconds = 0;
    state.yawOffset = 0;
    state.pitchOffset = 0;
    state.zoomMultiplier = 1;
    state.targetOffset = [0, 0, 0];
    state.desiredYawOffset = 0;
    state.desiredPitchOffset = 0;
    state.desiredZoomMultiplier = 1;
    state.desiredTargetOffset = [0, 0, 0];
    state.trackedTarget = [0, 0, 0];
    state.trackedVelocity = [0, 0, 0];
    state.hasTrackingTarget = false;
    state.trackedFollowYaw = 0;
    state.followYawCycle = -1;
    updateCameraModeUI();
  }

  function cycleCameraMode() {
    const nextIndex = (CAMERA_MODES.indexOf(state.cameraMode) + 1) % CAMERA_MODES.length;
    state.cameraMode = CAMERA_MODES[nextIndex];
    updateCameraModeUI();
    announcer.textContent = `Camera mode ${state.cameraMode.toLowerCase()}.`;
  }

  function clamp(value, minimum, maximum) {
    return Math.min(maximum, Math.max(minimum, value));
  }

  function mix(start, end, amount) {
    return start + (end - start) * amount;
  }

  function smoothstep(value) {
    const clamped = clamp(value, 0, 1);
    return clamped * clamped * (3 - 2 * clamped);
  }

  function smootherstep(value) {
    const clamped = clamp(value, 0, 1);
    return clamped ** 3 * (clamped * (clamped * 6 - 15) + 10);
  }

  function followWeightAt(seconds) {
    const local = Math.max(0, seconds) % FREE_CYCLE_SECONDS;
    if (local < 8) return 0;
    if (local < 32) return smootherstep((local - 8) / 24);
    if (local < 64) return 1;
    if (local < 88) return 1 - smootherstep((local - 64) / 24);
    return 0;
  }

  function macroYawAt(seconds) {
    return 0.020 * seconds + 0.12 * Math.sin(seconds / 32);
  }

  function freeCameraPose(seconds) {
    const followWeight = followWeightAt(seconds);
    const macroPose = {
      yaw: macroYawAt(seconds),
      pitch: 0.54 + 0.20 * Math.sin(seconds / 36) + 0.04 * Math.sin(seconds / 16),
      zoom: 2 * (1.02 + 0.08 * Math.sin(seconds / 30) + 0.03 * Math.sin(seconds / 14 + 0.7)),
      target: [0, 0, 0],
      framing: [0, 0]
    };
    const followPose = {
      yaw: state.trackedFollowYaw,
      pitch: 0.05,
      zoom: 30,
      target: state.trackedTarget,
      framing: [0, 0]
    };
    return {
      yaw: mix(macroPose.yaw, followPose.yaw, followWeight),
      pitch: mix(macroPose.pitch, followPose.pitch, followWeight),
      zoom: mix(macroPose.zoom, followPose.zoom, followWeight),
      target: macroPose.target.map((value, index) => mix(value, followPose.target[index], followWeight)),
      framing: [0, 0]
    };
  }

  function cinematicCameraPose(seconds) {
    const local = ((seconds % CINEMATIC_DURATION_SECONDS) + CINEMATIC_DURATION_SECONDS) % CINEMATIC_DURATION_SECONDS;
    for (let index = 0; index < CINEMATIC_KEYFRAMES.length - 1; index += 1) {
      const [startTime, start] = CINEMATIC_KEYFRAMES[index];
      const [endTime, end] = CINEMATIC_KEYFRAMES[index + 1];
      if (local <= endTime) {
        const amount = smoothstep((local - startTime) / (endTime - startTime));
        return {
          yaw: mix(start.yaw, end.yaw, amount),
          pitch: mix(start.pitch, end.pitch, amount),
          zoom: mix(start.zoom, end.zoom, amount),
          target: start.target.map((value, axis) => mix(value, end.target[axis], amount)),
          framing: start.framing.map((value, axis) => mix(value, end.framing[axis], amount))
        };
      }
    }
    return CINEMATIC_KEYFRAMES[CINEMATIC_KEYFRAMES.length - 1][1];
  }

  function cameraPoseAt(seconds) {
    let base;
    if (state.cameraMode === "FREE") base = freeCameraPose(seconds);
    else if (state.cameraMode === "CINEMATIC") base = cinematicCameraPose(seconds);
    else base = { yaw: 0, pitch: 0.42, zoom: 1, target: [0, 0, 0], framing: [0, 0] };

    return {
      yaw: base.yaw + state.yawOffset,
      pitch: clamp(base.pitch + state.pitchOffset, -1.25, 1.25),
      zoom: clamp(base.zoom * state.zoomMultiplier, 0.18, 36),
      target: base.target.map((value, index) => value + state.targetOffset[index]),
      framing: base.framing
    };
  }

  function advanceManualMotion(elapsed) {
    const blend = 1 - Math.exp(-MANUAL_RESPONSE_PER_SECOND * Math.max(0, elapsed));
    state.yawOffset += (state.desiredYawOffset - state.yawOffset) * blend;
    state.pitchOffset += (state.desiredPitchOffset - state.pitchOffset) * blend;
    state.zoomMultiplier += (state.desiredZoomMultiplier - state.zoomMultiplier) * blend;
    state.targetOffset = state.targetOffset.map((value, index) => (
      value + (state.desiredTargetOffset[index] - value) * blend
    ));
  }

  function followStreamAt(seconds, streamCount) {
    const cycle = Math.floor(Math.max(0, seconds) / FREE_CYCLE_SECONDS);
    return (11 + cycle * 37) % streamCount;
  }

  function updateFollowTarget(target, direction, elapsed, seconds) {
    if (!state.hasTrackingTarget) {
      state.trackedTarget = target.slice();
      state.trackedVelocity = [0, 0, 0];
      state.hasTrackingTarget = true;
    } else {
      let desiredVelocity = target.map((value, index) => (value - state.trackedTarget[index]) * 0.65);
      const desiredSpeed = Math.hypot(...desiredVelocity);
      const normalizedSpeedLimit = 2 / 17.4;
      if (desiredSpeed > normalizedSpeedLimit) {
        desiredVelocity = desiredVelocity.map((value) => value * normalizedSpeedLimit / desiredSpeed);
      }
      const velocityBlend = 1 - Math.exp(-2 * Math.max(0, elapsed));
      state.trackedVelocity = state.trackedVelocity.map((value, index) => (
        value + (desiredVelocity[index] - value) * velocityBlend
      ));
      state.trackedTarget = state.trackedTarget.map((value, index) => value + state.trackedVelocity[index] * elapsed);
    }

    const [dx, , dz] = direction;
    const cycle = Math.floor(Math.max(0, seconds) / FREE_CYCLE_SECONDS);
    if (cycle !== state.followYawCycle && Math.abs(dx) + Math.abs(dz) > 1e-9) {
      const desiredYaw = Math.atan2(dz, dx);
      const referenceYaw = macroYawAt(cycle * FREE_CYCLE_SECONDS + 20);
      const turns = Math.round((referenceYaw - desiredYaw) / (2 * Math.PI));
      state.trackedFollowYaw = desiredYaw + turns * 2 * Math.PI;
      state.followYawCycle = cycle;
    }
  }

  function selectSystem(index, shouldAnnounce = true) {
    const normalizedIndex = (index + SYSTEMS.length) % SYSTEMS.length;
    const system = SYSTEMS[normalizedIndex];
    state.currentIndex = normalizedIndex;
    state.position = 0;
    stateReadout.textContent = "x 0.00 · y 0.00 · z 0.00";
    updateSystemPanel(system, normalizedIndex);
    resetCamera();
    stage.classList.add("is-loading");

    const sequence = ++state.loadSequence;
    requestAnimationFrame(() => {
      if (sequence !== state.loadSequence) return;
      try {
        state.trajectory = buildTrajectory(system);
        stage.classList.remove("is-loading");
        history.replaceState(null, "", `${location.pathname}${location.search}#${system.slug}`);
        if (shouldAnnounce) announcer.textContent = `${system.title} loaded.`;
        const activeButton = systemOptions[normalizedIndex];
        activeButton.scrollIntoView({ behavior: reducedMotionQuery.matches ? "auto" : "smooth", block: "nearest", inline: "center" });
      } catch (error) {
        stage.classList.remove("is-loading");
        announcer.textContent = `Unable to draw ${system.title}.`;
        console.error(error);
      }
    });
  }

  function resizeCanvas() {
    const bounds = stage.getBoundingClientRect();
    state.width = Math.max(1, bounds.width);
    state.height = Math.max(1, bounds.height);
    state.dpr = Math.min(window.devicePixelRatio || 1, 2);
    canvas.width = Math.round(state.width * state.dpr);
    canvas.height = Math.round(state.height * state.dpr);
    canvas.style.width = `${state.width}px`;
    canvas.style.height = `${state.height}px`;
  }

  function drawBackground() {
    const { width, height } = state;
    context.save();
    context.globalCompositeOperation = "source-over";
    for (const star of stars) {
      context.fillStyle = star.gold
        ? `rgba(221, 179, 91, ${star.alpha * 0.7})`
        : `rgba(163, 222, 203, ${star.alpha})`;
      context.beginPath();
      context.arc(star.x * width, star.y * height, star.size, 0, Math.PI * 2);
      context.fill();
    }

    const centerX = width * 0.5;
    const centerY = height * (width < 780 ? 0.58 : 0.49);
    const radius = Math.min(width, height) * 0.29;
    context.strokeStyle = "rgba(125, 235, 201, 0.035)";
    context.lineWidth = 1;
    context.beginPath();
    context.arc(centerX, centerY, radius, 0, Math.PI * 2);
    context.stroke();
    context.setLineDash([2, 10]);
    context.strokeStyle = "rgba(221, 179, 91, 0.045)";
    context.beginPath();
    context.arc(centerX, centerY, radius * 0.74, 0, Math.PI * 2);
    context.stroke();
    context.setLineDash([]);
    context.restore();
  }

  function sampleTrajectory(points, count, position) {
    const wrapped = ((position % count) + count) % count;
    const index = Math.floor(wrapped);
    const t = wrapped - index;
    const sample = [0, 0, 0];
    const tangent = [0, 0, 0];

    for (let axis = 0; axis < 3; axis += 1) {
      const point = (pointIndex) => points[pointIndex * 3 + axis];
      if (count >= 4 && index >= 1 && index <= count - 3) {
        const p0 = point(index - 1);
        const p1 = point(index);
        const p2 = point(index + 1);
        const p3 = point(index + 2);
        const t2 = t * t;
        const t3 = t2 * t;
        sample[axis] = 0.5 * (
          2 * p1 + (-p0 + p2) * t + (2 * p0 - 5 * p1 + 4 * p2 - p3) * t2
          + (-p0 + 3 * p1 - 3 * p2 + p3) * t3
        );
        tangent[axis] = 0.5 * (
          (-p0 + p2) + 2 * (2 * p0 - 5 * p1 + 4 * p2 - p3) * t
          + 3 * (-p0 + 3 * p1 - 3 * p2 + p3) * t2
        );
      } else {
        const nextIndex = Math.min(index + 1, count - 1);
        const start = point(index);
        const delta = index === count - 1
          ? point(count - 1) - point(count - 2)
          : point(nextIndex) - start;
        sample[axis] = start + delta * t;
        tangent[axis] = delta;
      }
    }
    return { position: sample, tangent };
  }

  function streamCountForViewport() {
    return state.width < 650 ? 3 : 5;
  }

  function createProjector(pose) {
    const { width, height } = state;
    const { yaw, pitch, zoom, target, framing } = pose;
    const cosineYaw = Math.cos(yaw);
    const sineYaw = Math.sin(yaw);
    const cosinePitch = Math.cos(pitch);
    const sinePitch = Math.sin(pitch);
    const centerX = width * 0.5 + framing[0] * width * 0.5;
    const centerY = height * (width < 780 ? 0.58 : 0.49) - framing[1] * height * 0.5;
    const focalLength = Math.min(width, height) * 0.98;
    const displayZoom = zoom / 2;

    return (coordinates) => {
      const x = coordinates[0] - target[0];
      const y = coordinates[1] - target[1];
      const z = coordinates[2] - target[2];
      const yawX = cosineYaw * x + sineYaw * z;
      const yawZ = -sineYaw * x + cosineYaw * z;
      const pitchY = cosinePitch * y - sinePitch * yawZ;
      const pitchZ = sinePitch * y + cosinePitch * yawZ;
      const cameraDistance = Math.max(0.72, 2.7 + pitchZ * 0.55);
      const scale = focalLength * displayZoom / cameraDistance;
      return [centerX + yawX * scale, centerY - pitchY * scale, cameraDistance];
    };
  }

  function drawAttractor(pose) {
    const trajectory = state.trajectory;
    if (!trajectory) return;

    const system = SYSTEMS[state.currentIndex];
    const points = trajectory.points;
    const count = trajectory.count;
    const project = createProjector(pose);
    const streamCount = streamCountForViewport();
    const pointsPerStream = Math.max(120, Math.floor(state.trailLength / streamCount));
    const chunks = 5;
    const chunkLength = Math.max(24, Math.floor(pointsPerStream / chunks));
    const sampleStep = Math.max(1, Math.ceil(state.trailLength / (state.width < 650 ? 5000 : 9000)));
    const baseHead = Math.floor(state.position) % count;
    const displayZoom = pose.zoom / 2;

    context.save();
    context.lineCap = "round";
    context.lineJoin = "round";
    context.globalCompositeOperation = "lighter";

    for (let stream = 0; stream < streamCount; stream += 1) {
      const streamPosition = (state.position + Math.floor(stream * count / streamCount)) % count;
      const head = Math.floor(streamPosition);
      const sampledHead = sampleTrajectory(points, count, streamPosition).position;
      const colour = system.palette[stream % system.palette.length];

      for (let chunk = 0; chunk < chunks; chunk += 1) {
        const start = head - pointsPerStream + chunk * chunkLength;
        const end = chunk === chunks - 1 ? head : start + chunkLength;
        const fade = (chunk + 1) / chunks;
        context.beginPath();
        let hasPoint = false;
        let previousWrapped = -1;

        for (let cursor = start; cursor <= end; cursor += sampleStep) {
          const wrapped = ((cursor % count) + count) % count;
          const pointOffset = wrapped * 3;
          const projected = project([points[pointOffset], points[pointOffset + 1], points[pointOffset + 2]]);
          if (!hasPoint || wrapped < previousWrapped) {
            context.moveTo(projected[0], projected[1]);
            hasPoint = true;
          } else {
            context.lineTo(projected[0], projected[1]);
          }
          previousWrapped = wrapped;
        }

        if (chunk === chunks - 1 && streamPosition - head > 1e-8 && head < count - 1) {
          const projectedHead = project(sampledHead);
          context.lineTo(projectedHead[0], projectedHead[1]);
        }

        const alpha = 0.025 + fade * fade * 0.12;
        context.strokeStyle = `rgba(${colour[0]}, ${colour[1]}, ${colour[2]}, ${alpha})`;
        context.lineWidth = 4.2 + displayZoom * 2.2;
        context.stroke();
        context.strokeStyle = `rgba(${colour[0]}, ${colour[1]}, ${colour[2]}, ${0.08 + fade * 0.42})`;
        context.lineWidth = 0.55 + displayZoom * 0.42;
        context.stroke();
      }

      const projectedHead = project(sampledHead);
      const haloRadius = 4.5 + Math.min(displayZoom, 8) * 3.6;
      const gradient = context.createRadialGradient(
        projectedHead[0], projectedHead[1], 0,
        projectedHead[0], projectedHead[1], haloRadius
      );
      gradient.addColorStop(0, "rgba(245, 255, 251, 1)");
      gradient.addColorStop(0.16, `rgba(${colour[0]}, ${colour[1]}, ${colour[2]}, 0.95)`);
      gradient.addColorStop(1, `rgba(${colour[0]}, ${colour[1]}, ${colour[2]}, 0)`);
      context.fillStyle = gradient;
      context.beginPath();
      context.arc(projectedHead[0], projectedHead[1], haloRadius, 0, Math.PI * 2);
      context.fill();
    }

    context.restore();

    if (state.frame % 6 === 0) {
      const offset = baseHead * 3;
      const rawX = points[offset] * trajectory.radius + trajectory.center[0];
      const rawY = points[offset + 1] * trajectory.radius + trajectory.center[1];
      const rawZ = points[offset + 2] * trajectory.radius + trajectory.center[2];
      stateReadout.textContent = `x ${formatCoordinate(rawX)} · y ${formatCoordinate(rawY)} · z ${formatCoordinate(rawZ)}`;
    }
  }

  function formatCoordinate(value) {
    if (Math.abs(value) >= 100) return value.toFixed(0);
    if (Math.abs(value) >= 10) return value.toFixed(1);
    return value.toFixed(2);
  }

  function drawFrame(timestamp) {
    if (state.lastTimestamp === null) state.lastTimestamp = timestamp;
    const elapsed = Math.min(0.05, Math.max(0, (timestamp - state.lastTimestamp) / 1000));
    state.lastTimestamp = timestamp;
    state.frame += 1;

    const advancing = !state.paused && !document.hidden;
    if (advancing && state.trajectory) {
      state.position = (state.position + elapsed * 45 * state.speed) % state.trajectory.count;
      state.cameraSeconds += elapsed;
    }
    if (!document.hidden) advanceManualMotion(elapsed);

    if (state.trajectory) {
      const followStream = followStreamAt(state.cameraSeconds, CAMERA_STREAM_COUNT);
      const followPosition = state.position + Math.floor(followStream * state.trajectory.count / CAMERA_STREAM_COUNT);
      const sample = sampleTrajectory(state.trajectory.points, state.trajectory.count, followPosition);
      if (advancing || !state.hasTrackingTarget) {
        updateFollowTarget(sample.position, sample.tangent, advancing ? elapsed : 0, state.cameraSeconds);
      }
    }

    const pose = cameraPoseAt(state.cameraSeconds);

    context.setTransform(state.dpr, 0, 0, state.dpr, 0, 0);
    context.clearRect(0, 0, state.width, state.height);
    drawBackground();
    drawAttractor(pose);
    requestAnimationFrame(drawFrame);
  }

  function togglePause(force) {
    state.paused = typeof force === "boolean" ? force : !state.paused;
    updatePauseUI();
    announcer.textContent = state.paused ? "Animation paused." : "Animation playing.";
  }

  function resetAll() {
    state.position = 0;
    state.speed = 1;
    speedControl.value = "1";
    speedOutput.value = "1×";
    speedOutput.textContent = "1×";
    resetCamera();
    if (!reducedMotionQuery.matches) state.paused = false;
    updatePauseUI();
    announcer.textContent = "Attractor, speed, and camera reset.";
  }

  function queueOrbit(deltaX, deltaY) {
    state.desiredYawOffset += deltaX * 0.006;
    state.desiredPitchOffset = clamp(state.desiredPitchOffset + deltaY * 0.004, -0.88, 0.88);
  }

  function queuePan(deltaX, deltaY) {
    state.desiredTargetOffset[0] -= deltaX * (0.035 / 30);
    state.desiredTargetOffset[1] += deltaY * (0.035 / 30);
  }

  function queueDolly(wheelSteps) {
    state.desiredZoomMultiplier = clamp(
      state.desiredZoomMultiplier * (1.1 ** wheelSteps),
      0.18,
      10
    );
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
    pointers.set(event.pointerId, {
      x: event.clientX,
      y: event.clientY,
      pointerType: event.pointerType,
      pan: event.pointerType === "mouse" && event.shiftKey
    });
    state.pinchDistance = pointerDistance();
    dismissGestureHint();
  });

  canvas.addEventListener("pointermove", (event) => {
    const previous = pointers.get(event.pointerId);
    if (!previous) return;
    const current = {
      x: event.clientX,
      y: event.clientY,
      pointerType: previous.pointerType,
      pan: previous.pan || (previous.pointerType === "mouse" && event.shiftKey)
    };
    pointers.set(event.pointerId, current);

    if (pointers.size === 1) {
      const deltaX = event.clientX - previous.x;
      const deltaY = event.clientY - previous.y;
      if (current.pan) queuePan(deltaX, deltaY);
      else queueOrbit(deltaX, deltaY);
    } else {
      const distance = pointerDistance();
      if (distance && state.pinchDistance) {
        state.desiredZoomMultiplier = clamp(
          state.desiredZoomMultiplier * distance / state.pinchDistance,
          0.18,
          10
        );
      }
      state.pinchDistance = distance;
    }
  });

  function releasePointer(event) {
    pointers.delete(event.pointerId);
    state.pinchDistance = pointerDistance();
    if (event.type !== "lostpointercapture" && typeof canvas.hasPointerCapture === "function" && canvas.hasPointerCapture(event.pointerId)) {
      canvas.releasePointerCapture(event.pointerId);
    }
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
    queueDolly(-pixels / 100);
    dismissGestureHint();
  }, { passive: false });
  canvas.addEventListener("dblclick", () => resetCamera(true));

  function fullscreenElement() {
    return document.fullscreenElement
      || document.webkitFullscreenElement
      || document.webkitCurrentFullScreenElement
      || null;
  }

  function updateFullscreenUI() {
    const active = fullscreenElement() === stage;
    const ambientControl = document.querySelector(".ambient-audio");
    if (ambientControl) (active ? stage : document.body).appendChild(ambientControl);
    fullscreenButton.setAttribute("aria-pressed", String(active));
    fullscreenLabel.textContent = active ? "Exit full screen" : "Full screen";
    fullscreenButton.title = active ? "Exit full screen (F / F11)" : "Enter full screen (F / F11)";
    requestAnimationFrame(resizeCanvas);
  }

  async function toggleFullscreen() {
    try {
      if (fullscreenElement()) {
        if (document.exitFullscreen) await document.exitFullscreen();
        else if (document.webkitExitFullscreen) document.webkitExitFullscreen();
        else if (document.webkitCancelFullScreen) document.webkitCancelFullScreen();
      } else if (stage.requestFullscreen) {
        await stage.requestFullscreen();
      } else if (stage.webkitRequestFullscreen) {
        stage.webkitRequestFullscreen();
      } else if (stage.webkitRequestFullScreen) {
        stage.webkitRequestFullScreen();
      } else {
        announcer.textContent = "Full screen is not available in this browser.";
      }
    } catch (error) {
      announcer.textContent = "The browser did not allow full screen.";
      console.error(error);
    }
  }

  pauseButton.addEventListener("click", () => togglePause());
  previousButton.addEventListener("click", () => selectSystem(state.currentIndex - 1));
  nextButton.addEventListener("click", () => selectSystem(state.currentIndex + 1));
  resetButton.addEventListener("click", resetAll);
  cameraModeButton.addEventListener("click", cycleCameraMode);
  fullscreenButton.addEventListener("click", toggleFullscreen);
  document.addEventListener("fullscreenchange", updateFullscreenUI);
  document.addEventListener("webkitfullscreenchange", updateFullscreenUI);

  speedControl.addEventListener("input", () => {
    state.speed = Number(speedControl.value);
    speedOutput.value = `${state.speed}×`;
    speedOutput.textContent = `${state.speed}×`;
  });

  trailControl.addEventListener("input", () => {
    state.trailLength = Number(trailControl.value);
    const label = numberFormat.format(state.trailLength);
    trailOutput.value = label;
    trailOutput.textContent = label;
  });

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
    if (target instanceof HTMLElement && target.closest("input, button, dialog, a")) return;

    if (event.key === "ArrowDown" || event.key === "ArrowRight") {
      event.preventDefault();
      selectSystem(state.currentIndex + 1);
    } else if (event.key === "ArrowUp" || event.key === "ArrowLeft") {
      event.preventDefault();
      selectSystem(state.currentIndex - 1);
    } else if (event.code === "Space" || event.key.toLowerCase() === "p") {
      event.preventDefault();
      togglePause();
    } else if (event.key.toLowerCase() === "r") {
      resetAll();
    } else if (event.key.toLowerCase() === "c") {
      cycleCameraMode();
    } else if (event.key.toLowerCase() === "f" || event.key === "F11") {
      event.preventDefault();
      toggleFullscreen();
    } else if (/^[1-9]$/.test(event.key)) {
      state.speed = Number(event.key);
      speedControl.value = event.key;
      speedOutput.value = `${event.key}×`;
      speedOutput.textContent = `${event.key}×`;
    } else if (event.key === "+" || event.key === "=") {
      queueDolly(1);
    } else if (event.key === "-" || event.key === "_") {
      queueDolly(-1);
    }
  });

  reducedMotionQuery.addEventListener("change", (event) => {
    if (event.matches) {
      state.paused = true;
      updatePauseUI();
      announcer.textContent = "Reduced motion enabled. Animation paused.";
    }
  });

  document.addEventListener("visibilitychange", () => {
    state.lastTimestamp = null;
  });

  const resizeObserver = new ResizeObserver(resizeCanvas);
  resizeObserver.observe(stage);
  resizeCanvas();
  updatePauseUI();
  updateCameraModeUI();
  updateFullscreenUI();

  const requestedSlug = location.hash.replace(/^#/, "");
  const requestedIndex = SYSTEMS.findIndex((system) => system.slug === requestedSlug);
  selectSystem(requestedIndex >= 0 ? requestedIndex : 0, false);
  requestAnimationFrame(drawFrame);
})();
