(() => {
  "use strict";

  const canvas = document.querySelector("#surfaceCanvas");
  const chart = document.querySelector("#metricChart");
  const stage = document.querySelector("#stage");
  const loadingPanel = document.querySelector("#loadingPanel");
  const loadingText = document.querySelector("#loadingText");
  const errorPanel = document.querySelector("#errorPanel");
  const solverStatus = document.querySelector("#solverStatus");
  const timeline = document.querySelector("#timeline");
  const timelineOutput = document.querySelector("#timelineOutput");
  const playButton = document.querySelector("#playButton");
  const playIcon = document.querySelector("#playIcon");
  const playLabel = document.querySelector("#playLabel");
  const stepBackButton = document.querySelector("#stepBackButton");
  const stepForwardButton = document.querySelector("#stepForwardButton");
  const meshButton = document.querySelector("#meshButton");
  const resetButton = document.querySelector("#resetButton");
  const fullscreenButton = document.querySelector("#fullscreenButton");
  const speedSelect = document.querySelector("#speedSelect");
  const keysButton = document.querySelector("#keysButton");
  const keyGuide = document.querySelector("#keyGuide");
  const announcer = document.querySelector("#announcer");
  const readouts = {
    frame: document.querySelector("#frameReadout"),
    time: document.querySelector("#timeReadout"),
    area: document.querySelector("#areaReadout"),
    volume: document.querySelector("#volumeReadout"),
    quality: document.querySelector("#qualityReadout")
  };
  const verification = {
    area: document.querySelector("#checkArea"),
    orientation: document.querySelector("#checkOrientation"),
    volume: document.querySelector("#checkVolume")
  };

  const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");
  const chartContext = chart.getContext("2d");
  const state = {
    trajectory: null,
    diagnostics: null,
    gl: null,
    renderer: null,
    progress: 0,
    playing: !reducedMotion.matches,
    speed: 1,
    showMesh: true,
    lastTimestamp: 0,
    playDuration: 12,
    dirty: true,
    raf: 0,
    width: 0,
    height: 0,
    camera: {
      yaw: -0.72,
      pitch: 0.34,
      distance: 5.5,
      target: [0, 0, 0]
    },
    pointers: new Map(),
    pinchDistance: 0,
    fallbackFullscreen: false
  };

  function announce(message) {
    announcer.textContent = "";
    window.requestAnimationFrame(() => { announcer.textContent = message; });
  }

  function clamp(value, minimum, maximum) {
    return Math.min(maximum, Math.max(minimum, value));
  }

  function parseTrajectory(buffer) {
    const view = new DataView(buffer);
    const magic = Array.from(new Uint8Array(buffer, 0, 8), (value) => String.fromCharCode(value)).join("");
    if (magic !== "BGNPFEM1") throw new Error(`未知的轨迹格式：${magic}`);
    const version = view.getUint32(8, true);
    const vertexCount = view.getUint32(12, true);
    const triangleCount = view.getUint32(16, true);
    const frameCount = view.getUint32(20, true);
    const metricCount = view.getUint32(24, true);
    const dt = view.getFloat32(32, true);
    const totalTime = view.getFloat32(36, true);
    if (version !== 1 || metricCount !== 6) throw new Error(`不支持的轨迹版本：${version}`);
    let offset = 40;
    const indices = new Uint32Array(buffer, offset, triangleCount * 3);
    offset += indices.byteLength;
    const times = new Float32Array(buffer, offset, frameCount);
    offset += times.byteLength;
    const metrics = new Float32Array(buffer, offset, frameCount * metricCount);
    offset += metrics.byteLength;
    const positions = new Float32Array(buffer, offset, frameCount * vertexCount * 3);
    offset += positions.byteLength;
    if (offset !== buffer.byteLength) throw new Error("轨迹文件长度与头信息不一致");
    return { version, vertexCount, triangleCount, frameCount, metricCount, dt, totalTime, indices, times, metrics, positions };
  }

  function createShader(gl, type, source) {
    const shader = gl.createShader(type);
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      const message = gl.getShaderInfoLog(shader);
      gl.deleteShader(shader);
      throw new Error(`WebGL 着色器编译失败：${message}`);
    }
    return shader;
  }

  function createProgram(gl, vertexSource, fragmentSource) {
    const program = gl.createProgram();
    gl.attachShader(program, createShader(gl, gl.VERTEX_SHADER, vertexSource));
    gl.attachShader(program, createShader(gl, gl.FRAGMENT_SHADER, fragmentSource));
    gl.linkProgram(program);
    if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
      const message = gl.getProgramInfoLog(program);
      gl.deleteProgram(program);
      throw new Error(`WebGL 程序链接失败：${message}`);
    }
    return program;
  }

  function uniqueEdges(indices) {
    const edgeSet = new Set();
    const edges = [];
    const add = (first, second) => {
      const a = Math.min(first, second);
      const b = Math.max(first, second);
      const key = `${a}:${b}`;
      if (edgeSet.has(key)) return;
      edgeSet.add(key);
      edges.push(a, b);
    };
    for (let index = 0; index < indices.length; index += 3) {
      add(indices[index], indices[index + 1]);
      add(indices[index + 1], indices[index + 2]);
      add(indices[index + 2], indices[index]);
    }
    return new Uint32Array(edges);
  }

  function createRenderer(gl, trajectory) {
    const surfaceProgram = createProgram(gl, `#version 300 es
      precision highp float;
      layout(location=0) in vec3 a_position;
      layout(location=1) in vec3 a_normal;
      uniform mat4 u_viewProjection;
      uniform vec3 u_eye;
      out vec3 v_normal;
      out vec3 v_view;
      out vec3 v_position;
      void main() {
        v_normal = a_normal;
        v_position = a_position;
        v_view = u_eye - a_position;
        gl_Position = u_viewProjection * vec4(a_position, 1.0);
      }
    `, `#version 300 es
      precision highp float;
      in vec3 v_normal;
      in vec3 v_view;
      in vec3 v_position;
      out vec4 outColor;
      void main() {
        vec3 n = normalize(v_normal);
        vec3 viewDir = normalize(v_view);
        vec3 lightA = normalize(vec3(-0.42, 0.83, 0.34));
        vec3 lightB = normalize(vec3(0.62, 0.20, -0.76));
        float diffuse = max(dot(n, lightA), 0.0);
        float rim = pow(1.0 - abs(dot(n, viewDir)), 2.35);
        float fill = max(dot(n, lightB), 0.0);
        float heightTone = clamp((v_position.y + 1.65) / 3.3, 0.0, 1.0);
        vec3 deep = vec3(0.035, 0.18, 0.145);
        vec3 mint = vec3(0.30, 0.84, 0.68);
        vec3 cyan = vec3(0.18, 0.63, 0.68);
        vec3 gold = vec3(0.86, 0.66, 0.30);
        vec3 color = mix(deep, mix(cyan, mint, heightTone), 0.20 + 0.72 * diffuse);
        color += fill * vec3(0.018, 0.07, 0.06);
        color += rim * mix(mint, gold, 0.18) * 0.42;
        outColor = vec4(color, 1.0);
      }
    `);
    const lineProgram = createProgram(gl, `#version 300 es
      precision highp float;
      layout(location=0) in vec3 a_position;
      uniform mat4 u_viewProjection;
      void main() { gl_Position = u_viewProjection * vec4(a_position, 1.0); }
    `, `#version 300 es
      precision highp float;
      out vec4 outColor;
      void main() { outColor = vec4(0.34, 0.92, 0.80, 0.67); }
    `);

    const vao = gl.createVertexArray();
    gl.bindVertexArray(vao);
    const positionBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, positionBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, trajectory.vertexCount * 3 * 4, gl.DYNAMIC_DRAW);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
    const normalBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, normalBuffer);
    gl.bufferData(gl.ARRAY_BUFFER, trajectory.vertexCount * 3 * 4, gl.DYNAMIC_DRAW);
    gl.enableVertexAttribArray(1);
    gl.vertexAttribPointer(1, 3, gl.FLOAT, false, 0, 0);
    const triangleBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, triangleBuffer);
    gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, trajectory.indices, gl.STATIC_DRAW);
    gl.bindVertexArray(null);

    const lineVao = gl.createVertexArray();
    gl.bindVertexArray(lineVao);
    gl.bindBuffer(gl.ARRAY_BUFFER, positionBuffer);
    gl.enableVertexAttribArray(0);
    gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 0, 0);
    const edgeIndices = uniqueEdges(trajectory.indices);
    const edgeBuffer = gl.createBuffer();
    gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, edgeBuffer);
    gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, edgeIndices, gl.STATIC_DRAW);
    gl.bindVertexArray(null);

    return {
      surfaceProgram,
      lineProgram,
      vao,
      lineVao,
      positionBuffer,
      normalBuffer,
      edgeIndices,
      surfaceVP: gl.getUniformLocation(surfaceProgram, "u_viewProjection"),
      surfaceEye: gl.getUniformLocation(surfaceProgram, "u_eye"),
      lineVP: gl.getUniformLocation(lineProgram, "u_viewProjection"),
      interpolated: new Float32Array(trajectory.vertexCount * 3),
      normals: new Float32Array(trajectory.vertexCount * 3)
    };
  }

  function perspective(fieldOfView, aspect, near, far) {
    const f = 1 / Math.tan(fieldOfView / 2);
    const range = 1 / (near - far);
    return new Float32Array([
      f / aspect, 0, 0, 0,
      0, f, 0, 0,
      0, 0, (far + near) * range, -1,
      0, 0, 2 * far * near * range, 0
    ]);
  }

  function normalize3(vector) {
    const length = Math.hypot(vector[0], vector[1], vector[2]) || 1;
    return [vector[0] / length, vector[1] / length, vector[2] / length];
  }

  function cross3(first, second) {
    return [first[1] * second[2] - first[2] * second[1], first[2] * second[0] - first[0] * second[2], first[0] * second[1] - first[1] * second[0]];
  }

  function lookAt(eye, center, up) {
    const z = normalize3([eye[0] - center[0], eye[1] - center[1], eye[2] - center[2]]);
    const x = normalize3(cross3(up, z));
    const y = cross3(z, x);
    return new Float32Array([
      x[0], y[0], z[0], 0,
      x[1], y[1], z[1], 0,
      x[2], y[2], z[2], 0,
      -(x[0] * eye[0] + x[1] * eye[1] + x[2] * eye[2]),
      -(y[0] * eye[0] + y[1] * eye[1] + y[2] * eye[2]),
      -(z[0] * eye[0] + z[1] * eye[1] + z[2] * eye[2]),
      1
    ]);
  }

  function multiply4(first, second) {
    const output = new Float32Array(16);
    for (let column = 0; column < 4; column += 1) {
      for (let row = 0; row < 4; row += 1) {
        let value = 0;
        for (let index = 0; index < 4; index += 1) value += first[index * 4 + row] * second[column * 4 + index];
        output[column * 4 + row] = value;
      }
    }
    return output;
  }

  function cameraMatrices() {
    const { yaw, pitch, distance, target } = state.camera;
    const cosine = Math.cos(pitch);
    const eye = [
      target[0] + distance * cosine * Math.sin(yaw),
      target[1] + distance * Math.sin(pitch),
      target[2] + distance * cosine * Math.cos(yaw)
    ];
    const projection = perspective(38 * Math.PI / 180, Math.max(.01, state.width / state.height), .05, 60);
    return { eye, viewProjection: multiply4(projection, lookAt(eye, target, [0, 1, 0])) };
  }

  function interpolatePositions() {
    const data = state.trajectory;
    const renderer = state.renderer;
    const framePosition = state.progress * (data.frameCount - 1);
    const firstFrame = Math.floor(framePosition);
    const secondFrame = Math.min(data.frameCount - 1, firstFrame + 1);
    const alpha = framePosition - firstFrame;
    const valuesPerFrame = data.vertexCount * 3;
    const firstOffset = firstFrame * valuesPerFrame;
    const secondOffset = secondFrame * valuesPerFrame;
    for (let index = 0; index < valuesPerFrame; index += 1) {
      renderer.interpolated[index] = data.positions[firstOffset + index] * (1 - alpha) + data.positions[secondOffset + index] * alpha;
    }
    renderer.normals.fill(0);
    const position = renderer.interpolated;
    const normal = renderer.normals;
    const indices = data.indices;
    for (let index = 0; index < indices.length; index += 3) {
      const i0 = indices[index] * 3;
      const i1 = indices[index + 1] * 3;
      const i2 = indices[index + 2] * 3;
      const ax = position[i1] - position[i0];
      const ay = position[i1 + 1] - position[i0 + 1];
      const az = position[i1 + 2] - position[i0 + 2];
      const bx = position[i2] - position[i0];
      const by = position[i2 + 1] - position[i0 + 1];
      const bz = position[i2 + 2] - position[i0 + 2];
      const nx = ay * bz - az * by;
      const ny = az * bx - ax * bz;
      const nz = ax * by - ay * bx;
      for (const vertex of [i0, i1, i2]) {
        normal[vertex] += nx;
        normal[vertex + 1] += ny;
        normal[vertex + 2] += nz;
      }
    }
    for (let index = 0; index < normal.length; index += 3) {
      const length = Math.hypot(normal[index], normal[index + 1], normal[index + 2]) || 1;
      normal[index] /= length;
      normal[index + 1] /= length;
      normal[index + 2] /= length;
    }
    return { firstFrame, secondFrame, alpha, framePosition };
  }

  function metricAt(frame, metric) {
    return state.trajectory.metrics[frame * state.trajectory.metricCount + metric];
  }

  function interpolatedMetric(frameState, metric) {
    return metricAt(frameState.firstFrame, metric) * (1 - frameState.alpha) + metricAt(frameState.secondFrame, metric) * frameState.alpha;
  }

  function updateReadouts(frameState) {
    const data = state.trajectory;
    const time = data.totalTime * state.progress;
    const area = interpolatedMetric(frameState, 0);
    const volume = interpolatedMetric(frameState, 1);
    const quality = interpolatedMetric(frameState, 2);
    const initialArea = metricAt(0, 0);
    const initialVolume = metricAt(0, 1);
    const volumeError = volume / initialVolume - 1;
    readouts.frame.textContent = `m = ${Math.round(frameState.framePosition)}`;
    readouts.time.textContent = time.toFixed(5);
    readouts.area.textContent = (area / initialArea).toFixed(6);
    readouts.volume.textContent = `${volumeError >= 0 ? "+" : "−"}${Math.abs(volumeError * 100).toFixed(3)}%`;
    readouts.quality.textContent = quality.toFixed(4);
    timeline.value = state.progress.toFixed(4);
    const percent = Math.round(state.progress * 100);
    timelineOutput.textContent = `${percent}%`;
    timeline.style.setProperty("--range-progress", `${percent}%`);
    canvas.dataset.frame = String(Math.round(frameState.framePosition));
    canvas.dataset.time = time.toFixed(8);
    canvas.dataset.areaRatio = (area / initialArea).toFixed(9);
    canvas.dataset.volumeError = volumeError.toExponential(6);
    canvas.dataset.minimumQuality = quality.toFixed(8);
    canvas.dataset.cameraYaw = state.camera.yaw.toFixed(6);
    canvas.dataset.cameraPitch = state.camera.pitch.toFixed(6);
    canvas.dataset.cameraDistance = state.camera.distance.toFixed(6);
  }

  function drawChart() {
    if (!state.trajectory || !chartContext) return;
    const rect = chart.getBoundingClientRect();
    const scale = Math.min(window.devicePixelRatio || 1, 2);
    const width = Math.max(1, Math.round(rect.width * scale));
    const height = Math.max(1, Math.round(rect.height * scale));
    if (chart.width !== width || chart.height !== height) {
      chart.width = width;
      chart.height = height;
    }
    const context = chartContext;
    context.setTransform(scale, 0, 0, scale, 0, 0);
    context.clearRect(0, 0, rect.width, rect.height);
    const data = state.trajectory;
    const padding = 5;
    const plotWidth = rect.width - padding * 2;
    const plotHeight = rect.height - padding * 2;
    const initialArea = metricAt(0, 0);
    const finalArea = metricAt(data.frameCount - 1, 0) / initialArea;
    let maximumVolumeError = 0;
    const initialVolume = metricAt(0, 1);
    for (let frame = 0; frame < data.frameCount; frame += 1) maximumVolumeError = Math.max(maximumVolumeError, Math.abs(metricAt(frame, 1) / initialVolume - 1));
    const drawSeries = (color, valueAt) => {
      context.beginPath();
      for (let frame = 0; frame < data.frameCount; frame += 1) {
        const x = padding + (frame / (data.frameCount - 1)) * plotWidth;
        const y = padding + clamp(valueAt(frame), 0, 1) * plotHeight;
        if (frame === 0) context.moveTo(x, y); else context.lineTo(x, y);
      }
      context.strokeStyle = color;
      context.lineWidth = 1.15;
      context.stroke();
    };
    drawSeries("rgba(125,235,201,.88)", (frame) => (1 - metricAt(frame, 0) / initialArea) / Math.max(1e-9, 1 - finalArea));
    drawSeries("rgba(221,179,91,.8)", (frame) => Math.abs(metricAt(frame, 1) / initialVolume - 1) / Math.max(1e-9, maximumVolumeError));
    const markerX = padding + state.progress * plotWidth;
    context.beginPath();
    context.moveTo(markerX, 2);
    context.lineTo(markerX, rect.height - 2);
    context.strokeStyle = "rgba(231,242,237,.58)";
    context.lineWidth = 1;
    context.stroke();
  }

  function render() {
    if (!state.trajectory || !state.renderer || !state.gl || !state.width || !state.height) return;
    const gl = state.gl;
    const renderer = state.renderer;
    const frameState = interpolatePositions();
    const matrices = cameraMatrices();
    gl.viewport(0, 0, canvas.width, canvas.height);
    gl.clearColor(0.008, 0.028, 0.024, 0);
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    gl.enable(gl.DEPTH_TEST);
    gl.enable(gl.CULL_FACE);
    gl.cullFace(gl.BACK);

    gl.bindBuffer(gl.ARRAY_BUFFER, renderer.positionBuffer);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, renderer.interpolated);
    gl.bindBuffer(gl.ARRAY_BUFFER, renderer.normalBuffer);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, renderer.normals);

    gl.useProgram(renderer.surfaceProgram);
    gl.uniformMatrix4fv(renderer.surfaceVP, false, matrices.viewProjection);
    gl.uniform3fv(renderer.surfaceEye, matrices.eye);
    gl.bindVertexArray(renderer.vao);
    gl.enable(gl.POLYGON_OFFSET_FILL);
    gl.polygonOffset(1, 1);
    gl.drawElements(gl.TRIANGLES, state.trajectory.indices.length, gl.UNSIGNED_INT, 0);
    gl.disable(gl.POLYGON_OFFSET_FILL);

    if (state.showMesh) {
      gl.useProgram(renderer.lineProgram);
      gl.uniformMatrix4fv(renderer.lineVP, false, matrices.viewProjection);
      gl.bindVertexArray(renderer.lineVao);
      gl.drawElements(gl.LINES, renderer.edgeIndices.length, gl.UNSIGNED_INT, 0);
    }
    gl.bindVertexArray(null);
    updateReadouts(frameState);
    drawChart();
    state.dirty = false;
  }

  function tick(timestamp) {
    const elapsed = state.lastTimestamp ? Math.min(.1, (timestamp - state.lastTimestamp) / 1000) : 0;
    state.lastTimestamp = timestamp;
    if (state.playing && state.trajectory) {
      state.progress += elapsed * state.speed / state.playDuration;
      if (state.progress > 1) state.progress %= 1;
      state.dirty = true;
    }
    if (state.dirty) render();
    state.raf = window.requestAnimationFrame(tick);
  }

  function updatePlaybackUI() {
    playButton.setAttribute("aria-pressed", String(state.playing));
    playIcon.textContent = state.playing ? "Ⅱ" : "▶";
    playLabel.textContent = state.playing ? "暂停" : "播放";
  }

  function setPlaying(playing, shouldAnnounce = true) {
    state.playing = Boolean(playing);
    state.lastTimestamp = 0;
    updatePlaybackUI();
    if (shouldAnnounce) announce(state.playing ? "动画继续" : "动画暂停");
  }

  function setProgress(progress, pause = false) {
    state.progress = clamp(progress, 0, 1);
    if (pause) setPlaying(false, false);
    state.dirty = true;
  }

  function step(direction) {
    if (!state.trajectory) return;
    const frame = Math.round(state.progress * (state.trajectory.frameCount - 1));
    setProgress(clamp(frame + direction, 0, state.trajectory.frameCount - 1) / (state.trajectory.frameCount - 1), true);
    announce(`有限元时间步 ${Math.round(state.progress * (state.trajectory.frameCount - 1))}`);
  }

  function resetCamera() {
    state.camera.yaw = -0.72;
    state.camera.pitch = 0.34;
    state.camera.distance = 5.5;
    state.camera.target = [0, 0, 0];
    state.dirty = true;
  }

  function resetAll() {
    setProgress(0, true);
    resetCamera();
    announce("时间与相机已重置");
  }

  function toggleMesh() {
    state.showMesh = !state.showMesh;
    meshButton.setAttribute("aria-pressed", String(state.showMesh));
    meshButton.textContent = `网格 · ${state.showMesh ? "ON" : "OFF"}`;
    state.dirty = true;
    announce(state.showMesh ? "三角网格已显示" : "三角网格已隐藏");
  }

  async function toggleFullscreen() {
    try {
      if (document.fullscreenElement) {
        await document.exitFullscreen();
      } else if (stage.requestFullscreen) {
        await stage.requestFullscreen();
      } else {
        state.fallbackFullscreen = !state.fallbackFullscreen;
        stage.classList.toggle("is-immersive", state.fallbackFullscreen);
        document.body.style.overflow = state.fallbackFullscreen ? "hidden" : "";
        updateFullscreenUI();
      }
    } catch (_error) {
      state.fallbackFullscreen = !state.fallbackFullscreen;
      stage.classList.toggle("is-immersive", state.fallbackFullscreen);
      document.body.style.overflow = state.fallbackFullscreen ? "hidden" : "";
      updateFullscreenUI();
    }
  }

  function updateFullscreenUI() {
    const active = Boolean(document.fullscreenElement || state.fallbackFullscreen);
    fullscreenButton.setAttribute("aria-pressed", String(active));
    fullscreenButton.textContent = active ? "退出全屏" : "全屏";
    state.dirty = true;
    window.setTimeout(resize, 50);
  }

  function resize() {
    const rect = canvas.getBoundingClientRect();
    if (!rect.width || !rect.height) return;
    const scale = Math.min(window.devicePixelRatio || 1, 2);
    const width = Math.round(rect.width * scale);
    const height = Math.round(rect.height * scale);
    if (canvas.width !== width || canvas.height !== height) {
      canvas.width = width;
      canvas.height = height;
    }
    state.width = rect.width;
    state.height = rect.height;
    state.dirty = true;
  }

  function pointerDistance() {
    const pointers = [...state.pointers.values()];
    if (pointers.length < 2) return 0;
    return Math.hypot(pointers[0].x - pointers[1].x, pointers[0].y - pointers[1].y);
  }

  canvas.addEventListener("pointerdown", (event) => {
    canvas.setPointerCapture(event.pointerId);
    state.pointers.set(event.pointerId, { x: event.clientX, y: event.clientY, shift: event.shiftKey });
    state.pinchDistance = pointerDistance();
  });
  canvas.addEventListener("pointermove", (event) => {
    const previous = state.pointers.get(event.pointerId);
    if (!previous) return;
    const dx = event.clientX - previous.x;
    const dy = event.clientY - previous.y;
    state.pointers.set(event.pointerId, { x: event.clientX, y: event.clientY, shift: event.shiftKey });
    if (state.pointers.size >= 2) {
      const nextDistance = pointerDistance();
      if (state.pinchDistance > 0 && nextDistance > 0) state.camera.distance = clamp(state.camera.distance * state.pinchDistance / nextDistance, 2.7, 12);
      state.pinchDistance = nextDistance;
    } else if (event.shiftKey || previous.shift) {
      const scale = state.camera.distance * .0013;
      state.camera.target[0] -= dx * scale;
      state.camera.target[1] += dy * scale;
    } else {
      state.camera.yaw -= dx * .007;
      state.camera.pitch = clamp(state.camera.pitch - dy * .007, -1.35, 1.35);
    }
    state.dirty = true;
  });
  const releasePointer = (event) => {
    state.pointers.delete(event.pointerId);
    state.pinchDistance = pointerDistance();
  };
  canvas.addEventListener("pointerup", releasePointer);
  canvas.addEventListener("pointercancel", releasePointer);
  canvas.addEventListener("wheel", (event) => {
    event.preventDefault();
    state.camera.distance = clamp(state.camera.distance * Math.exp(event.deltaY * .001), 2.7, 12);
    state.dirty = true;
  }, { passive: false });
  canvas.addEventListener("dblclick", () => { resetCamera(); announce("相机已重置"); });

  playButton.addEventListener("click", () => setPlaying(!state.playing));
  stepBackButton.addEventListener("click", () => step(-1));
  stepForwardButton.addEventListener("click", () => step(1));
  meshButton.addEventListener("click", toggleMesh);
  resetButton.addEventListener("click", resetAll);
  fullscreenButton.addEventListener("click", toggleFullscreen);
  speedSelect.addEventListener("change", () => { state.speed = Number(speedSelect.value) || 1; announce(`播放速度 ${state.speed} 倍`); });
  timeline.addEventListener("input", () => setProgress(Number(timeline.value), true));
  keysButton.addEventListener("click", () => {
    if (typeof keyGuide.showModal === "function") keyGuide.showModal();
    keysButton.setAttribute("aria-expanded", "true");
  });
  keyGuide.addEventListener("close", () => keysButton.setAttribute("aria-expanded", "false"));
  document.addEventListener("fullscreenchange", updateFullscreenUI);
  document.addEventListener("keydown", (event) => {
    const tag = event.target && event.target.tagName;
    if (["INPUT", "SELECT", "TEXTAREA"].includes(tag)) return;
    const key = event.key.toLowerCase();
    if (key === "p" || key === " ") { event.preventDefault(); setPlaying(!state.playing); }
    else if (key === "arrowleft") { event.preventDefault(); step(-1); }
    else if (key === "arrowright") { event.preventDefault(); step(1); }
    else if (key === "m") toggleMesh();
    else if (key === "r") resetAll();
    else if (key === "f") toggleFullscreen();
    else if (key === "escape" && state.fallbackFullscreen) toggleFullscreen();
  });
  reducedMotion.addEventListener("change", (event) => { if (event.matches) setPlaying(false, false); });
  new ResizeObserver(resize).observe(canvas);

  function installDiagnostics() {
    const data = state.trajectory;
    const diagnostics = state.diagnostics;
    solverStatus.textContent = `${data.vertexCount} 顶点 · ${data.triangleCount.toLocaleString()} 三角形 · τ=${data.dt.toExponential(0)}`;
    verification.area.textContent = diagnostics.surface_area_monotone ? `${data.frameCount - 1} 步表面积全部下降` : "表面积检查失败";
    verification.orientation.textContent = diagnostics.orientation_preserved ? "所有三角形定向保持" : "检测到三角形翻转";
    verification.volume.textContent = `最大体积漂移 ${(diagnostics.max_relative_volume_drift * 100).toFixed(3)}%`;
    canvas.dataset.renderer = "webgl2";
    canvas.dataset.scheme = "bgn-pfem-surface-diffusion";
    canvas.dataset.vertexCount = String(data.vertexCount);
    canvas.dataset.triangleCount = String(data.triangleCount);
    canvas.dataset.frameCount = String(data.frameCount);
    canvas.dataset.timeStep = String(data.dt);
    canvas.dataset.surfaceAreaMonotone = String(diagnostics.surface_area_monotone);
    canvas.dataset.energyInequalitySatisfied = String(diagnostics.energy_inequality_satisfied);
    canvas.dataset.orientationPreserved = String(diagnostics.orientation_preserved);
    canvas.dataset.maximumAreaIncrease = String(diagnostics.max_area_increase);
    canvas.dataset.maximumVolumeDrift = String(diagnostics.max_relative_volume_drift);
    canvas.dataset.minimumTriangleQuality = String(diagnostics.minimum_triangle_quality);
  }

  async function initialise() {
    try {
      loadingText.textContent = "载入 1,200 个三角形与 321 个有限元状态…";
      const [trajectoryResponse, diagnosticsResponse] = await Promise.all([fetch("trajectory.bin"), fetch("trajectory-diagnostics.json")]);
      if (!trajectoryResponse.ok) throw new Error(`轨迹载入失败（HTTP ${trajectoryResponse.status}）`);
      if (!diagnosticsResponse.ok) throw new Error(`诊断数据载入失败（HTTP ${diagnosticsResponse.status}）`);
      const [buffer, diagnostics] = await Promise.all([trajectoryResponse.arrayBuffer(), diagnosticsResponse.json()]);
      state.trajectory = parseTrajectory(buffer);
      state.diagnostics = diagnostics;
      const gl = canvas.getContext("webgl2", { antialias: true, alpha: true, depth: true, powerPreference: "high-performance" });
      if (!gl) throw new Error("当前浏览器或设备没有可用的 WebGL 2 上下文");
      state.gl = gl;
      state.renderer = createRenderer(gl, state.trajectory);
      installDiagnostics();
      resize();
      updatePlaybackUI();
      render();
      loadingPanel.classList.add("is-hidden");
      window.setTimeout(() => { loadingPanel.hidden = true; }, 450);
      announce("BGN 有限元轨迹已载入");
    } catch (error) {
      loadingPanel.hidden = true;
      errorPanel.hidden = false;
      errorPanel.textContent = `无法启动可视化：${error.message}`;
      solverStatus.textContent = "载入失败";
      console.error(error);
    }
  }

  state.raf = window.requestAnimationFrame(tick);
  initialise();
})();
