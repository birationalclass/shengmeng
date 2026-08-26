(() => {
  "use strict";

  const glCanvas = document.querySelector("#glCanvas");
  const fallbackCanvas = document.querySelector("#fallbackCanvas");
  const stage = document.querySelector("#fractalStage");
  const traceCanvas = document.querySelector("#traceCanvas");
  const pauseButton = document.querySelector("#pauseButton");
  const pauseIcon = document.querySelector("#pauseIcon");
  const pauseLabel = document.querySelector("#pauseLabel");
  const resetButton = document.querySelector("#resetButton");
  const zoomInButton = document.querySelector("#zoomInButton");
  const zoomOutButton = document.querySelector("#zoomOutButton");
  const fullscreenButton = document.querySelector("#fullscreenButton");
  const iterationSlider = document.querySelector("#iterationSlider");
  const iterationOutput = document.querySelector("#iterationOutput");
  const rendererName = document.querySelector("#rendererName");
  const rendererLight = document.querySelector("#rendererLight");
  const motionState = document.querySelector("#motionState");
  const cRealOutput = document.querySelector("#cReal");
  const cImaginaryOutput = document.querySelector("#cImaginary");
  const zoomOutput = document.querySelector("#zoomValue");
  const iterationValue = document.querySelector("#iterationValue");
  const timeOutput = document.querySelector("#timeValue");
  const paletteOutput = document.querySelector("#paletteValue");
  const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");

  const state = {
    elapsed: 0,
    paused: reducedMotion.matches,
    zoom: 1,
    targetZoom: 1,
    panX: 0,
    panY: 0,
    iterations: 64,
    dirty: true
  };

  const clamp = (value, minimum, maximum) => Math.max(minimum, Math.min(maximum, value));
  const smoothstep = (minimum, maximum, value) => {
    const amount = clamp((value - minimum) / (maximum - minimum), 0, 1);
    return amount * amount * (3 - 2 * amount);
  };
  const mix = (first, second, amount) => first * (1 - amount) + second * amount;

  function complexParameter(time) {
    return {
      real: 1.1 * (.5 * Math.cos(.01 * time) - .25 * Math.cos(.02 * time)),
      imaginary: 1.1 * (.5 * Math.sin(.01 * time) - .25 * Math.sin(.02 * time))
    };
  }

  function palettePhase(time) {
    const cycleTime = ((time % 184) + 184) % 184;
    const blueCycle = Math.floor(time / 184) % 2 === 1;
    let accent = 0;
    if (cycleTime >= 95 && cycleTime < 165) {
      const fadeIn = smoothstep(95, 105, cycleTime);
      const fadeOut = 1 - smoothstep(155, 165, cycleTime);
      accent = clamp(fadeIn * fadeOut, 0, 1);
    }
    return { cycleTime, blueCycle, accent, blueAmount: blueCycle ? accent : 0 };
  }

  const vertexSource = `#version 300 es
    in vec2 aPosition;
    void main() {
      gl_Position = vec4(aPosition, 0.0, 1.0);
    }
  `;

  const fragmentSource = `#version 300 es
    precision highp float;
    out vec4 outColor;
    uniform float uTime;
    uniform vec2 uResolution;
    uniform float uZoom;
    uniform vec2 uPan;
    uniform int uIterations;

    vec2 multiplyComplex(vec2 first, vec2 second) {
      return vec2(
        first.x * second.x - first.y * second.y,
        first.x * second.y + first.y * second.x
      );
    }

    void main() {
      vec2 point = 1.2 * (2.0 * gl_FragCoord.xy - uResolution.xy) / uResolution.y;
      point = point / uZoom + uPan;

      float parameterTime = 0.1 * uTime;
      vec2 c = 1.1 * vec2(
        0.5 * cos(0.1 * parameterTime) - 0.25 * cos(0.2 * parameterTime),
        0.5 * sin(0.1 * parameterTime) - 0.25 * sin(0.2 * parameterTime)
      );
      vec2 z = point;
      vec4 minimumDistance = vec4(1000.0);

      for (int index = 0; index < 128; index += 1) {
        if (index >= uIterations) break;
        z = c + multiplyComplex(z, z);
        minimumDistance = min(minimumDistance, vec4(
          abs(z.y + 0.5 * sin(z.x)),
          abs(1.0 + z.x + 0.5 * sin(z.y)),
          dot(z, z),
          length(fract(z) - 0.5)
        ));
      }

      float cycleTime = mod(uTime, 184.0);
      float blueCycle = mod(floor(uTime / 184.0), 2.0);
      float accentAmount = 0.0;
      if (cycleTime >= 95.0 && cycleTime < 165.0) {
        float fadeIn = smoothstep(95.0, 105.0, cycleTime);
        float fadeOut = 1.0 - smoothstep(155.0, 165.0, cycleTime);
        accentAmount = clamp(fadeIn * fadeOut, 0.0, 1.0);
      }

      float blueAmount = blueCycle * accentAmount;
      vec3 warmBase = vec3(minimumDistance.w) + vec3(0.05);
      vec3 blueBase = vec3(minimumDistance.w) * vec3(0.45, 0.70, 1.00) + vec3(0.02, 0.06, 0.10);
      vec3 colour = mix(warmBase, blueBase, blueAmount);
      vec3 accentX = mix(vec3(1.00, 0.80, 0.60), vec3(0.60, 0.40, 0.85), blueCycle);
      vec3 accentY = mix(vec3(0.72, 0.70, 0.60), vec3(0.00, 0.80, 0.90), blueCycle);
      colour = mix(colour, accentX, min(1.0, pow(minimumDistance.x * 0.25, 0.20)) * accentAmount);
      colour = mix(colour, accentY, min(1.0, pow(minimumDistance.y * 0.50, 0.50)) * accentAmount);
      colour = mix(colour, vec3(1.0), 1.0 - min(1.0, pow(minimumDistance.z, 0.15)));
      colour = 1.25 * colour * colour;
      colour = colour * colour * (3.0 - 2.0 * colour);
      outColor = vec4(colour, 1.0);
    }
  `;

  function compileShader(gl, type, source) {
    const shader = gl.createShader(type);
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      const message = gl.getShaderInfoLog(shader) || "Unknown shader error";
      gl.deleteShader(shader);
      throw new Error(message);
    }
    return shader;
  }

  function createWebGLRenderer() {
    const gl = glCanvas.getContext("webgl2", {
      alpha: false,
      antialias: false,
      depth: false,
      powerPreference: "high-performance",
      preserveDrawingBuffer: false
    });
    if (!gl) return null;

    const vertexShader = compileShader(gl, gl.VERTEX_SHADER, vertexSource);
    const fragmentShader = compileShader(gl, gl.FRAGMENT_SHADER, fragmentSource);
    const program = gl.createProgram();
    gl.attachShader(program, vertexShader);
    gl.attachShader(program, fragmentShader);
    gl.linkProgram(program);
    gl.deleteShader(vertexShader);
    gl.deleteShader(fragmentShader);
    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      const message = gl.getProgramInfoLog(program) || "Unknown program link error";
      gl.deleteProgram(program);
      throw new Error(message);
    }

    const vertexArray = gl.createVertexArray();
    gl.bindVertexArray(vertexArray);
    const buffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
    gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([
      -1, -1,
       1, -1,
       1,  1,
      -1,  1
    ]), gl.STATIC_DRAW);
    const position = gl.getAttribLocation(program, "aPosition");
    gl.enableVertexAttribArray(position);
    gl.vertexAttribPointer(position, 2, gl.FLOAT, false, 0, 0);

    const uniforms = {
      time: gl.getUniformLocation(program, "uTime"),
      resolution: gl.getUniformLocation(program, "uResolution"),
      zoom: gl.getUniformLocation(program, "uZoom"),
      pan: gl.getUniformLocation(program, "uPan"),
      iterations: gl.getUniformLocation(program, "uIterations")
    };

    return {
      type: "webgl2",
      draw() {
        gl.viewport(0, 0, glCanvas.width, glCanvas.height);
        gl.useProgram(program);
        gl.uniform1f(uniforms.time, state.elapsed);
        gl.uniform2f(uniforms.resolution, glCanvas.width, glCanvas.height);
        gl.uniform1f(uniforms.zoom, state.zoom);
        gl.uniform2f(uniforms.pan, state.panX, state.panY);
        gl.uniform1i(uniforms.iterations, state.iterations);
        gl.drawArrays(gl.TRIANGLE_FAN, 0, 4);
      }
    };
  }

  let fallbackContext = null;
  let fallbackBuffer = null;

  function cpuColour(pointX, pointY, parameter, phase) {
    let zx = pointX;
    let zy = pointY;
    let minimumX = 1000;
    let minimumY = 1000;
    let minimumRadius = 1000;
    let minimumGrid = 1000;

    for (let index = 0; index < state.iterations; index += 1) {
      const nextX = zx * zx - zy * zy + parameter.real;
      zy = 2 * zx * zy + parameter.imaginary;
      zx = nextX;
      if (!Number.isFinite(zx) || !Number.isFinite(zy)) break;
      minimumX = Math.min(minimumX, Math.abs(zy + .5 * Math.sin(zx)));
      minimumY = Math.min(minimumY, Math.abs(1 + zx + .5 * Math.sin(zy)));
      minimumRadius = Math.min(minimumRadius, zx * zx + zy * zy);
      const fractionalX = zx - Math.floor(zx) - .5;
      const fractionalY = zy - Math.floor(zy) - .5;
      minimumGrid = Math.min(minimumGrid, Math.hypot(fractionalX, fractionalY));
      if (Math.abs(zx) > 1e8 || Math.abs(zy) > 1e8) break;
    }

    let colour = [minimumGrid + .05, minimumGrid + .05, minimumGrid + .05];
    const blueBase = [minimumGrid * .45 + .02, minimumGrid * .7 + .06, minimumGrid + .1];
    colour = colour.map((value, index) => mix(value, blueBase[index], phase.blueAmount));
    const accentX = phase.blueCycle ? [.6, .4, .85] : [1, .8, .6];
    const accentY = phase.blueCycle ? [0, .8, .9] : [.72, .7, .6];
    const firstMix = Math.min(1, Math.pow(minimumX * .25, .2)) * phase.accent;
    const secondMix = Math.min(1, Math.pow(minimumY * .5, .5)) * phase.accent;
    const whiteMix = 1 - Math.min(1, Math.pow(minimumRadius, .15));
    colour = colour.map((value, index) => mix(value, accentX[index], firstMix));
    colour = colour.map((value, index) => mix(value, accentY[index], secondMix));
    colour = colour.map((value) => mix(value, 1, whiteMix));
    return colour.map((value) => {
      let mapped = 1.25 * value * value;
      mapped = mapped * mapped * (3 - 2 * mapped);
      return Math.round(clamp(mapped, 0, 1) * 255);
    });
  }

  function drawFallback() {
    if (!fallbackContext) return;
    const aspect = fallbackCanvas.width / fallbackCanvas.height;
    const width = Math.min(240, fallbackCanvas.width);
    const height = Math.max(1, Math.round(width / aspect));
    if (!fallbackBuffer || fallbackBuffer.width !== width || fallbackBuffer.height !== height) {
      fallbackBuffer = document.createElement("canvas");
      fallbackBuffer.width = width;
      fallbackBuffer.height = height;
    }
    const context = fallbackBuffer.getContext("2d");
    const image = context.createImageData(width, height);
    const parameter = complexParameter(state.elapsed);
    const phase = palettePhase(state.elapsed);
    for (let y = 0; y < height; y += 1) {
      for (let x = 0; x < width; x += 1) {
        const pointX = (1.2 * (2 * x - width) / height) / state.zoom + state.panX;
        const pointY = (1.2 * (height - 2 * y) / height) / state.zoom + state.panY;
        const colour = cpuColour(pointX, pointY, parameter, phase);
        const position = (y * width + x) * 4;
        image.data[position] = colour[0];
        image.data[position + 1] = colour[1];
        image.data[position + 2] = colour[2];
        image.data[position + 3] = 255;
      }
    }
    context.putImageData(image, 0, 0);
    fallbackContext.imageSmoothingEnabled = true;
    fallbackContext.drawImage(fallbackBuffer, 0, 0, fallbackCanvas.width, fallbackCanvas.height);
  }

  let renderer = null;

  function activateFallback(message) {
    renderer = { type: "canvas2d", draw: drawFallback };
    glCanvas.hidden = true;
    fallbackCanvas.hidden = false;
    fallbackContext = fallbackCanvas.getContext("2d", { alpha: false });
    rendererName.textContent = message || "Canvas 2D fallback";
    rendererLight.className = "fallback";
    state.dirty = true;
  }

  try {
    renderer = createWebGLRenderer();
    if (renderer) {
      rendererName.textContent = "WebGL2 / GPU";
      rendererLight.className = "ready";
    } else {
      activateFallback("Canvas 2D fallback");
    }
  } catch (error) {
    console.warn("WebGL2 initialization failed; using Canvas 2D.", error);
    activateFallback("Canvas 2D fallback");
  }

  glCanvas.addEventListener("webglcontextlost", (event) => {
    event.preventDefault();
    activateFallback("WebGL lost / Canvas 2D");
  });

  function resizeCanvases() {
    const bounds = stage.getBoundingClientRect();
    const pixelRatio = Math.min(window.devicePixelRatio || 1, renderer && renderer.type === "webgl2" ? 1.7 : 1);
    const width = Math.max(1, Math.round(bounds.width * pixelRatio));
    const height = Math.max(1, Math.round(bounds.height * pixelRatio));
    [glCanvas, fallbackCanvas].forEach((canvas) => {
      if (canvas.width !== width || canvas.height !== height) {
        canvas.width = width;
        canvas.height = height;
      }
    });
    state.dirty = true;
  }

  const resizeObserver = new ResizeObserver(resizeCanvases);
  resizeObserver.observe(stage);
  resizeCanvases();

  function drawTrace() {
    const context = traceCanvas.getContext("2d");
    const bounds = traceCanvas.getBoundingClientRect();
    const ratio = Math.min(window.devicePixelRatio || 1, 1.5);
    const width = Math.max(1, Math.round(bounds.width * ratio));
    const height = Math.max(1, Math.round(bounds.height * ratio));
    if (traceCanvas.width !== width || traceCanvas.height !== height) {
      traceCanvas.width = width;
      traceCanvas.height = height;
    }
    context.clearRect(0, 0, width, height);
    const padding = 22 * ratio;
    const mapPoint = (point) => ({
      x: padding + ((point.real + 1) / 2) * (width - 2 * padding),
      y: height - padding - ((point.imaginary + 1) / 2) * (height - 2 * padding)
    });

    context.strokeStyle = "rgba(175,220,202,.12)";
    context.lineWidth = ratio;
    context.beginPath();
    context.moveTo(padding, height / 2);
    context.lineTo(width - padding, height / 2);
    context.moveTo(width / 2, padding);
    context.lineTo(width / 2, height - padding);
    context.stroke();

    const period = Math.PI * 200;
    context.beginPath();
    for (let index = 0; index <= 360; index += 1) {
      const mapped = mapPoint(complexParameter((period * index) / 360));
      if (index === 0) context.moveTo(mapped.x, mapped.y);
      else context.lineTo(mapped.x, mapped.y);
    }
    context.strokeStyle = "rgba(130,240,207,.24)";
    context.lineWidth = ratio;
    context.stroke();

    const progress = ((state.elapsed % period) + period) % period;
    context.beginPath();
    const sampleCount = Math.max(1, Math.floor(360 * progress / period));
    for (let index = 0; index <= sampleCount; index += 1) {
      const mapped = mapPoint(complexParameter(progress * index / sampleCount));
      if (index === 0) context.moveTo(mapped.x, mapped.y);
      else context.lineTo(mapped.x, mapped.y);
    }
    context.strokeStyle = "rgba(231,185,92,.82)";
    context.lineWidth = 1.5 * ratio;
    context.stroke();

    const current = mapPoint(complexParameter(state.elapsed));
    const glow = context.createRadialGradient(current.x, current.y, 0, current.x, current.y, 11 * ratio);
    glow.addColorStop(0, "rgba(255,247,210,1)");
    glow.addColorStop(.24, "rgba(231,185,92,.95)");
    glow.addColorStop(1, "rgba(231,185,92,0)");
    context.fillStyle = glow;
    context.beginPath();
    context.arc(current.x, current.y, 11 * ratio, 0, Math.PI * 2);
    context.fill();
  }

  function updateInterface() {
    const parameter = complexParameter(state.elapsed);
    const phase = palettePhase(state.elapsed);
    cRealOutput.textContent = `${parameter.real >= 0 ? "+" : ""}${parameter.real.toFixed(6)}`;
    cImaginaryOutput.textContent = `${parameter.imaginary >= 0 ? "+" : ""}${parameter.imaginary.toFixed(6)}`;
    zoomOutput.textContent = `${state.zoom < 10 ? state.zoom.toFixed(2) : state.zoom.toFixed(1)}×`;
    iterationValue.textContent = String(state.iterations);
    iterationOutput.value = String(state.iterations);
    timeOutput.textContent = `${state.elapsed.toFixed(1)} s`;
    paletteOutput.textContent = phase.blueAmount > .5 ? "BLUE" : phase.accent > .5 ? "ACCENT" : "WARM";
    motionState.textContent = state.paused ? "PAUSED" : "RUNNING";
    pauseButton.setAttribute("aria-pressed", String(state.paused));
    pauseIcon.textContent = state.paused ? "▶" : "Ⅱ";
    pauseLabel.textContent = state.paused ? "继续" : "暂停";
    drawTrace();
  }

  function markDirty() {
    state.dirty = true;
  }

  function setZoom(nextZoom, clientX, clientY, canvas = glCanvas.hidden ? fallbackCanvas : glCanvas) {
    const boundedZoom = clamp(nextZoom, .1, 1000);
    if (clientX === undefined || clientY === undefined) {
      state.targetZoom = boundedZoom;
      markDirty();
      return;
    }
    const before = screenToWorld(clientX, clientY, state.targetZoom, canvas);
    state.targetZoom = boundedZoom;
    const after = screenToWorld(clientX, clientY, state.targetZoom, canvas);
    state.panX += before.x - after.x;
    state.panY += before.y - after.y;
    markDirty();
  }

  function screenToWorld(clientX, clientY, zoom, canvas) {
    const bounds = canvas.getBoundingClientRect();
    const localX = clientX - bounds.left;
    const localY = clientY - bounds.top;
    return {
      x: (1.2 * (2 * localX - bounds.width) / bounds.height) / zoom + state.panX,
      y: (1.2 * (bounds.height - 2 * localY) / bounds.height) / zoom + state.panY
    };
  }

  function togglePause() {
    state.paused = !state.paused;
    markDirty();
    updateInterface();
  }

  function resetExperiment() {
    state.elapsed = 0;
    state.zoom = 1;
    state.targetZoom = 1;
    state.panX = 0;
    state.panY = 0;
    state.iterations = 64;
    iterationSlider.value = "64";
    markDirty();
    updateInterface();
  }

  function toggleFullscreen() {
    if (document.fullscreenElement) {
      document.exitFullscreen().catch(() => {});
    } else {
      stage.requestFullscreen().catch(() => {});
    }
  }

  pauseButton.addEventListener("click", togglePause);
  resetButton.addEventListener("click", resetExperiment);
  zoomInButton.addEventListener("click", () => setZoom(state.targetZoom * 1.38));
  zoomOutButton.addEventListener("click", () => setZoom(state.targetZoom / 1.38));
  fullscreenButton.addEventListener("click", toggleFullscreen);
  iterationSlider.addEventListener("input", () => {
    state.iterations = Number(iterationSlider.value);
    iterationOutput.value = String(state.iterations);
    markDirty();
  });

  [glCanvas, fallbackCanvas].forEach((canvas) => {
    canvas.addEventListener("wheel", (event) => {
      event.preventDefault();
      const factor = Math.exp(-event.deltaY * .00135);
      setZoom(state.targetZoom * factor, event.clientX, event.clientY, canvas);
    }, { passive: false });

    canvas.addEventListener("dblclick", () => {
      state.zoom = 1;
      state.targetZoom = 1;
      state.panX = 0;
      state.panY = 0;
      markDirty();
    });
  });

  const pointers = new Map();
  let pinch = null;

  function activeCanvas() {
    return glCanvas.hidden ? fallbackCanvas : glCanvas;
  }

  function pointerDown(event) {
    if (event.currentTarget !== activeCanvas()) return;
    event.currentTarget.setPointerCapture(event.pointerId);
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
    if (pointers.size === 2) {
      const points = [...pointers.values()];
      const centerX = (points[0].x + points[1].x) / 2;
      const centerY = (points[0].y + points[1].y) / 2;
      pinch = {
        distance: Math.hypot(points[0].x - points[1].x, points[0].y - points[1].y),
        zoom: state.targetZoom,
        anchor: screenToWorld(centerX, centerY, state.targetZoom, event.currentTarget)
      };
    }
  }

  function pointerMove(event) {
    if (!pointers.has(event.pointerId) || event.currentTarget !== activeCanvas()) return;
    const previous = pointers.get(event.pointerId);
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
    const bounds = event.currentTarget.getBoundingClientRect();

    if (pointers.size === 1) {
      const deltaX = event.clientX - previous.x;
      const deltaY = event.clientY - previous.y;
      state.panX -= 2.4 * deltaX / (bounds.height * state.targetZoom);
      state.panY += 2.4 * deltaY / (bounds.height * state.targetZoom);
      markDirty();
      return;
    }

    if (pointers.size === 2 && pinch) {
      const points = [...pointers.values()];
      const centerX = (points[0].x + points[1].x) / 2;
      const centerY = (points[0].y + points[1].y) / 2;
      const distance = Math.max(1, Math.hypot(points[0].x - points[1].x, points[0].y - points[1].y));
      const nextZoom = clamp(pinch.zoom * distance / Math.max(1, pinch.distance), .1, 1000);
      const localX = centerX - bounds.left;
      const localY = centerY - bounds.top;
      state.targetZoom = nextZoom;
      state.panX = pinch.anchor.x - (1.2 * (2 * localX - bounds.width) / bounds.height) / nextZoom;
      state.panY = pinch.anchor.y - (1.2 * (bounds.height - 2 * localY) / bounds.height) / nextZoom;
      markDirty();
    }
  }

  function pointerUp(event) {
    pointers.delete(event.pointerId);
    if (pointers.size < 2) pinch = null;
  }

  [glCanvas, fallbackCanvas].forEach((canvas) => {
    canvas.addEventListener("pointerdown", pointerDown);
    canvas.addEventListener("pointermove", pointerMove);
    canvas.addEventListener("pointerup", pointerUp);
    canvas.addEventListener("pointercancel", pointerUp);
  });

  window.addEventListener("keydown", (event) => {
    const target = event.target;
    if (target instanceof HTMLInputElement || target instanceof HTMLButtonElement || target instanceof HTMLAnchorElement) return;
    const panStep = .13 / state.targetZoom;
    let handled = true;
    switch (event.key) {
      case " ":
      case "p":
      case "P": togglePause(); break;
      case "r":
      case "R": resetExperiment(); break;
      case "f":
      case "F": toggleFullscreen(); break;
      case "ArrowLeft": state.panX -= panStep; markDirty(); break;
      case "ArrowRight": state.panX += panStep; markDirty(); break;
      case "ArrowUp": state.panY += panStep; markDirty(); break;
      case "ArrowDown": state.panY -= panStep; markDirty(); break;
      case "+":
      case "=": setZoom(state.targetZoom * 1.38); break;
      case "-":
      case "_": setZoom(state.targetZoom / 1.38); break;
      case "[":
        state.iterations = Math.max(16, state.iterations - 1);
        iterationSlider.value = String(state.iterations);
        markDirty();
        break;
      case "]":
        state.iterations = Math.min(128, state.iterations + 1);
        iterationSlider.value = String(state.iterations);
        markDirty();
        break;
      default: handled = false;
    }
    if (handled) event.preventDefault();
  });

  const handleReducedMotionChange = (event) => {
    if (event.matches) state.paused = true;
    markDirty();
    updateInterface();
  };
  if (typeof reducedMotion.addEventListener === "function") reducedMotion.addEventListener("change", handleReducedMotionChange);
  else reducedMotion.addListener(handleReducedMotionChange);

  document.addEventListener("fullscreenchange", () => {
    fullscreenButton.querySelector("b").textContent = document.fullscreenElement ? "退出" : "全屏";
    window.setTimeout(resizeCanvases, 50);
  });

  let previousFrame = performance.now();
  let previousInterfaceUpdate = 0;
  let previousFallbackRender = 0;

  function frame(now) {
    const delta = Math.min(.05, Math.max(0, (now - previousFrame) / 1000));
    previousFrame = now;
    if (!state.paused && !document.hidden) state.elapsed += delta;

    const zoomDifference = state.targetZoom - state.zoom;
    if (Math.abs(zoomDifference) > .00001) {
      state.zoom += zoomDifference * (1 - Math.exp(-delta * 14));
      state.dirty = true;
    } else {
      state.zoom = state.targetZoom;
    }

    const shouldDraw = !state.paused || state.dirty;
    if (shouldDraw && renderer) {
      if (renderer.type === "webgl2" || now - previousFallbackRender > 150 || state.dirty) {
        renderer.draw();
        if (renderer.type === "canvas2d") previousFallbackRender = now;
      }
    }
    if (now - previousInterfaceUpdate > 90 || state.dirty) {
      updateInterface();
      previousInterfaceUpdate = now;
    }
    state.dirty = Math.abs(state.targetZoom - state.zoom) > .00001;
    window.requestAnimationFrame(frame);
  }

  const year = document.querySelector("#currentYear");
  if (year) year.textContent = String(new Date().getFullYear());
  updateInterface();
  window.requestAnimationFrame(frame);
})();
