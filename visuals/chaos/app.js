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
  const autoRotateButton = document.getElementById("autoRotateButton");
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
  const defaultCamera = { yaw: -0.72, pitch: -0.22, zoom: 1.0 };

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
    autoRotate: !reducedMotionQuery.matches,
    yaw: defaultCamera.yaw,
    pitch: defaultCamera.pitch,
    zoom: defaultCamera.zoom,
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

  function updateAutoRotateUI() {
    autoRotateButton.setAttribute("aria-pressed", String(state.autoRotate));
    autoRotateButton.textContent = state.autoRotate ? "Auto orbit" : "Manual orbit";
  }

  function resetCamera() {
    state.yaw = defaultCamera.yaw;
    state.pitch = defaultCamera.pitch;
    state.zoom = defaultCamera.zoom;
    state.autoRotate = !reducedMotionQuery.matches;
    updateAutoRotateUI();
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

  function createProjector() {
    const { width, height, yaw, pitch, zoom } = state;
    const cosineYaw = Math.cos(yaw);
    const sineYaw = Math.sin(yaw);
    const cosinePitch = Math.cos(pitch);
    const sinePitch = Math.sin(pitch);
    const centerX = width * 0.5;
    const centerY = height * (width < 780 ? 0.58 : 0.49);
    const focalLength = Math.min(width, height) * 0.98;

    return (points, pointIndex) => {
      const offset = pointIndex * 3;
      const x = points[offset];
      const y = points[offset + 1];
      const z = points[offset + 2];
      const yawX = cosineYaw * x + sineYaw * z;
      const yawZ = -sineYaw * x + cosineYaw * z;
      const pitchY = cosinePitch * y - sinePitch * yawZ;
      const pitchZ = sinePitch * y + cosinePitch * yawZ;
      const cameraDistance = Math.max(0.72, 2.7 + pitchZ * 0.55);
      const scale = focalLength * zoom / cameraDistance;
      return [centerX + yawX * scale, centerY - pitchY * scale, cameraDistance];
    };
  }

  function drawAttractor() {
    const trajectory = state.trajectory;
    if (!trajectory) return;

    const system = SYSTEMS[state.currentIndex];
    const points = trajectory.points;
    const count = trajectory.count;
    const project = createProjector();
    const streamCount = state.width < 650 ? 3 : 5;
    const pointsPerStream = Math.max(120, Math.floor(state.trailLength / streamCount));
    const chunks = 5;
    const chunkLength = Math.max(24, Math.floor(pointsPerStream / chunks));
    const sampleStep = Math.max(1, Math.ceil(state.trailLength / (state.width < 650 ? 5000 : 9000)));
    const baseHead = Math.floor(state.position) % count;

    context.save();
    context.lineCap = "round";
    context.lineJoin = "round";
    context.globalCompositeOperation = "lighter";

    for (let stream = 0; stream < streamCount; stream += 1) {
      const head = (baseHead + Math.floor(stream * count / streamCount)) % count;
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
          const projected = project(points, wrapped);
          if (!hasPoint || wrapped < previousWrapped) {
            context.moveTo(projected[0], projected[1]);
            hasPoint = true;
          } else {
            context.lineTo(projected[0], projected[1]);
          }
          previousWrapped = wrapped;
        }

        const alpha = 0.025 + fade * fade * 0.12;
        context.strokeStyle = `rgba(${colour[0]}, ${colour[1]}, ${colour[2]}, ${alpha})`;
        context.lineWidth = 4.2 + state.zoom * 2.2;
        context.stroke();
        context.strokeStyle = `rgba(${colour[0]}, ${colour[1]}, ${colour[2]}, ${0.08 + fade * 0.42})`;
        context.lineWidth = 0.55 + state.zoom * 0.42;
        context.stroke();
      }

      const projectedHead = project(points, head);
      const haloRadius = 4.5 + state.zoom * 3.6;
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

    if (!state.paused && state.trajectory) state.position = (state.position + elapsed * 45 * state.speed) % state.trajectory.count;
    if (state.autoRotate && !state.paused && pointers.size === 0) state.yaw += elapsed * 0.055;

    context.setTransform(state.dpr, 0, 0, state.dpr, 0, 0);
    context.clearRect(0, 0, state.width, state.height);
    drawBackground();
    drawAttractor();
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

  function setAutoRotate(value) {
    state.autoRotate = value;
    updateAutoRotateUI();
  }

  function setZoom(nextZoom) {
    state.zoom = Math.min(2.5, Math.max(0.5, nextZoom));
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
    canvas.setPointerCapture(event.pointerId);
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
    state.pinchDistance = pointerDistance();
    setAutoRotate(false);
    dismissGestureHint();
  });

  canvas.addEventListener("pointermove", (event) => {
    const previous = pointers.get(event.pointerId);
    if (!previous) return;
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });

    if (pointers.size === 1) {
      state.yaw += (event.clientX - previous.x) * 0.008;
      state.pitch = Math.min(1.25, Math.max(-1.25, state.pitch + (event.clientY - previous.y) * 0.007));
    } else {
      const distance = pointerDistance();
      if (distance && state.pinchDistance) setZoom(state.zoom * distance / state.pinchDistance);
      state.pinchDistance = distance;
    }
  });

  function releasePointer(event) {
    pointers.delete(event.pointerId);
    state.pinchDistance = pointerDistance();
  }

  canvas.addEventListener("pointerup", releasePointer);
  canvas.addEventListener("pointercancel", releasePointer);
  canvas.addEventListener("wheel", (event) => {
    event.preventDefault();
    setZoom(state.zoom * Math.exp(-event.deltaY * 0.0011));
    setAutoRotate(false);
    dismissGestureHint();
  }, { passive: false });
  canvas.addEventListener("dblclick", resetCamera);

  pauseButton.addEventListener("click", () => togglePause());
  previousButton.addEventListener("click", () => selectSystem(state.currentIndex - 1));
  nextButton.addEventListener("click", () => selectSystem(state.currentIndex + 1));
  resetButton.addEventListener("click", resetAll);
  autoRotateButton.addEventListener("click", () => setAutoRotate(!state.autoRotate));

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
    } else if (event.key.toLowerCase() === "a" || event.key.toLowerCase() === "c") {
      setAutoRotate(!state.autoRotate);
    } else if (/^[1-9]$/.test(event.key)) {
      state.speed = Number(event.key);
      speedControl.value = event.key;
      speedOutput.value = `${event.key}×`;
      speedOutput.textContent = `${event.key}×`;
      if (state.paused) togglePause(false);
    } else if (event.key === "+" || event.key === "=") {
      setZoom(state.zoom * 1.12);
      setAutoRotate(false);
    } else if (event.key === "-" || event.key === "_") {
      setZoom(state.zoom / 1.12);
      setAutoRotate(false);
    }
  });

  reducedMotionQuery.addEventListener("change", (event) => {
    if (event.matches) {
      state.paused = true;
      state.autoRotate = false;
      updatePauseUI();
      updateAutoRotateUI();
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
  updateAutoRotateUI();

  const requestedSlug = location.hash.replace(/^#/, "");
  const requestedIndex = SYSTEMS.findIndex((system) => system.slug === requestedSlug);
  selectSystem(requestedIndex >= 0 ? requestedIndex : 0, false);
  requestAnimationFrame(drawFrame);
})();
