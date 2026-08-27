(() => {
  "use strict";

  const ASSET_VERSION = "20260828-flow-10";

  function versionedAsset(path) {
    const url = new URL(path, window.location.href);
    url.searchParams.set("v", ASSET_VERSION);
    return url.toString();
  }

  const canvas = document.querySelector("#surfaceCanvas");
  const chart = document.querySelector("#metricChart");
  const stage = document.querySelector("#stage");
  const loadingPanel = document.querySelector("#loadingPanel");
  const loadingText = document.querySelector("#loadingText");
  const errorPanel = document.querySelector("#errorPanel");
  const solverStatus = document.querySelector("#solverStatus");
  const caseButtons = document.querySelector("#caseButtons");
  const caseCaption = document.querySelector("#caseCaption");
  const caseSourceNote = document.querySelector("#caseSourceNote");
  const activeCaseTitle = document.querySelector("#activeCaseTitle");
  const algorithmTitle = document.querySelector("#algorithmTitle");
  const algorithmDetails = Array.from(document.querySelectorAll(".algorithm-detail"));
  const topologyNote = document.querySelector("#topologyNote");
  const flowEyebrow = document.querySelector("#flowEyebrow");
  const equationTag = document.querySelector("#equationTag");
  const equationFirst = document.querySelector("#equationFirst");
  const equationSecond = document.querySelector("#equationSecond");
  const equationBody = document.querySelector("#equationBody");
  const equationNote = document.querySelector("#equationNote");
  const energyMetricLabel = document.querySelector("#energyMetricLabel");
  const volumeMetricLabel = document.querySelector("#volumeMetricLabel");
  const energyLegend = document.querySelector("#energyLegend");
  const volumeLegend = document.querySelector("#volumeLegend");
  const energyCheckNote = document.querySelector("#energyCheckNote");
  const volumeCheckNote = document.querySelector("#volumeCheckNote");
  const densitySelect = document.querySelector("#densitySelect");
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
    manifest: null,
    activeCase: null,
    activeVariant: null,
    density: "standard",
    loadSerial: 0,
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
    initialHoldRemaining: 0,
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
    const positionEncoding = view.getUint32(28, true);
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
    if (positionEncoding === 2) {
      const positionBits = new Uint32Array(buffer, positions.byteOffset, positions.length);
      const valuesPerFrame = vertexCount * 3;
      for (let frame = 1; frame < frameCount; frame += 1) {
        const current = frame * valuesPerFrame;
        const previous = current - valuesPerFrame;
        for (let index = 0; index < valuesPerFrame; index += 1) positionBits[current + index] ^= positionBits[previous + index];
      }
    } else if (positionEncoding !== 0) {
      throw new Error(`不支持的顶点编码：${positionEncoding}`);
    }
    return { version, vertexCount, triangleCount, frameCount, metricCount, dt, totalTime, indices, times, metrics, positions, positionEncoding };
  }

  function refineTrajectoryForDisplay(data) {
    const edgeMap = new Map();
    const edgePairs = [];
    const refinedIndices = [];
    const midpoint = (first, second) => {
      const a = Math.min(first, second);
      const b = Math.max(first, second);
      const key = `${a}:${b}`;
      if (!edgeMap.has(key)) {
        edgeMap.set(key, data.vertexCount + edgePairs.length);
        edgePairs.push([a, b]);
      }
      return edgeMap.get(key);
    };
    for (let index = 0; index < data.indices.length; index += 3) {
      const a = data.indices[index];
      const b = data.indices[index + 1];
      const c = data.indices[index + 2];
      const ab = midpoint(a, b);
      const bc = midpoint(b, c);
      const ca = midpoint(c, a);
      refinedIndices.push(a, ab, ca, ab, b, bc, ca, bc, c, ab, bc, ca);
    }
    const refinedVertexCount = data.vertexCount + edgePairs.length;
    const refinedPositions = new Float32Array(data.frameCount * refinedVertexCount * 3);
    const sourceFrameSize = data.vertexCount * 3;
    const refinedFrameSize = refinedVertexCount * 3;
    for (let frame = 0; frame < data.frameCount; frame += 1) {
      const sourceOffset = frame * sourceFrameSize;
      const refinedOffset = frame * refinedFrameSize;
      refinedPositions.set(data.positions.subarray(sourceOffset, sourceOffset + sourceFrameSize), refinedOffset);
      for (let edge = 0; edge < edgePairs.length; edge += 1) {
        const [first, second] = edgePairs[edge];
        const destination = refinedOffset + (data.vertexCount + edge) * 3;
        const firstOffset = sourceOffset + first * 3;
        const secondOffset = sourceOffset + second * 3;
        for (let axis = 0; axis < 3; axis += 1) refinedPositions[destination + axis] = 0.5 * (data.positions[firstOffset + axis] + data.positions[secondOffset + axis]);
      }
    }
    return {
      ...data,
      vertexCount: refinedVertexCount,
      triangleCount: refinedIndices.length / 3,
      indices: new Uint32Array(refinedIndices),
      positions: refinedPositions,
      displayRefinement: "one-to-four shared-edge midpoint subdivision"
    };
  }

  async function fetchTrajectoryBuffer(variant) {
    const response = await fetch(versionedAsset(variant.trajectory));
    if (!response.ok) throw new Error(`轨迹载入失败（HTTP ${response.status}）`);
    const payload = await response.arrayBuffer();
    const payloadMagic = Array.from(new Uint8Array(payload, 0, Math.min(8, payload.byteLength)), (value) => String.fromCharCode(value)).join("");
    if (payloadMagic === "BGNPFEM1") return payload;
    if (variant.compression === "gzip" && typeof DecompressionStream === "function") {
      const stream = new Blob([payload]).stream().pipeThrough(new DecompressionStream("gzip"));
      return new Response(stream).arrayBuffer();
    }
    if (variant.fallbackTrajectory) {
      const fallback = await fetch(versionedAsset(variant.fallbackTrajectory));
      if (!fallback.ok) throw new Error(`备用轨迹载入失败（HTTP ${fallback.status}）`);
      return fallback.arrayBuffer();
    }
    throw new Error("当前浏览器无法解压 gzip 轨迹");
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
      uniform float u_helfrich;
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
        if (u_helfrich > 0.5) {
          deep = vec3(0.20, 0.018, 0.026);
          mint = vec3(0.96, 0.24, 0.25);
          cyan = vec3(0.68, 0.055, 0.085);
          gold = vec3(1.00, 0.58, 0.28);
        }
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
      uniform vec4 u_lineColor;
      out vec4 outColor;
      void main() { outColor = u_lineColor; }
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
      triangleBuffer,
      edgeBuffer,
      edgeIndices,
      surfaceVP: gl.getUniformLocation(surfaceProgram, "u_viewProjection"),
      surfaceEye: gl.getUniformLocation(surfaceProgram, "u_eye"),
      surfaceHelfrich: gl.getUniformLocation(surfaceProgram, "u_helfrich"),
      lineVP: gl.getUniformLocation(lineProgram, "u_viewProjection"),
      lineColor: gl.getUniformLocation(lineProgram, "u_lineColor"),
      interpolated: new Float32Array(trajectory.vertexCount * 3),
      normals: new Float32Array(trajectory.vertexCount * 3)
    };
  }

  function disposeRenderer() {
    if (!state.renderer || !state.gl) return;
    const gl = state.gl;
    gl.deleteProgram(state.renderer.surfaceProgram);
    gl.deleteProgram(state.renderer.lineProgram);
    gl.deleteVertexArray(state.renderer.vao);
    gl.deleteVertexArray(state.renderer.lineVao);
    gl.deleteBuffer(state.renderer.positionBuffer);
    gl.deleteBuffer(state.renderer.normalBuffer);
    gl.deleteBuffer(state.renderer.triangleBuffer);
    gl.deleteBuffer(state.renderer.edgeBuffer);
    state.renderer = null;
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
    const primary = interpolatedMetric(frameState, 0);
    const volume = interpolatedMetric(frameState, 1);
    const quality = interpolatedMetric(frameState, 2);
    const geometricArea = interpolatedMetric(frameState, 3);
    const initialPrimary = metricAt(0, 0);
    const initialVolume = metricAt(0, 1);
    const initialGeometricArea = metricAt(0, 3);
    const volumeError = volume / initialVolume - 1;
    const areaError = geometricArea / initialGeometricArea - 1;
    const isHelfrich = state.activeCase && state.activeCase.flow === "helfrich";
    readouts.frame.textContent = `m = ${Math.round(frameState.framePosition)}`;
    readouts.time.textContent = time.toFixed(5);
    readouts.area.textContent = (primary / initialPrimary).toFixed(6);
    const signedPercent = (value) => `${value >= 0 ? "+" : "−"}${Math.abs(value * 100).toFixed(3)}%`;
    readouts.volume.textContent = isHelfrich
      ? `A ${signedPercent(areaError)} · V ${signedPercent(volumeError)}`
      : signedPercent(volumeError);
    readouts.quality.textContent = quality.toFixed(4);
    timeline.value = state.progress.toFixed(4);
    const percent = Math.round(state.progress * 100);
    timelineOutput.textContent = `${percent}%`;
    timeline.style.setProperty("--range-progress", `${percent}%`);
    canvas.dataset.frame = String(Math.round(frameState.framePosition));
    canvas.dataset.time = time.toFixed(8);
    canvas.dataset.areaRatio = (geometricArea / initialGeometricArea).toFixed(9);
    canvas.dataset.energyRatio = (primary / initialPrimary).toFixed(9);
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
    const initialPrimary = metricAt(0, 0);
    const finalPrimary = metricAt(data.frameCount - 1, 0) / initialPrimary;
    let maximumVolumeError = 0;
    let maximumAreaError = 0;
    const initialVolume = metricAt(0, 1);
    const initialGeometricArea = metricAt(0, 3);
    const isHelfrich = state.activeCase && state.activeCase.flow === "helfrich";
    for (let frame = 0; frame < data.frameCount; frame += 1) {
      maximumVolumeError = Math.max(maximumVolumeError, Math.abs(metricAt(frame, 1) / initialVolume - 1));
      maximumAreaError = Math.max(maximumAreaError, Math.abs(metricAt(frame, 3) / initialGeometricArea - 1));
    }
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
    drawSeries("rgba(125,235,201,.88)", (frame) => (1 - metricAt(frame, 0) / initialPrimary) / Math.max(1e-9, 1 - finalPrimary));
    drawSeries("rgba(221,179,91,.8)", (frame) => Math.abs(metricAt(frame, 1) / initialVolume - 1) / Math.max(1e-9, maximumVolumeError));
    if (isHelfrich) {
      drawSeries("rgba(238,140,105,.78)", (frame) => Math.abs(metricAt(frame, 3) / initialGeometricArea - 1) / Math.max(1e-9, maximumAreaError));
    }
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
    gl.uniform1f(renderer.surfaceHelfrich, state.activeCase && state.activeCase.flow === "helfrich" ? 1 : 0);
    gl.bindVertexArray(renderer.vao);
    gl.enable(gl.POLYGON_OFFSET_FILL);
    gl.polygonOffset(1, 1);
    gl.drawElements(gl.TRIANGLES, state.trajectory.indices.length, gl.UNSIGNED_INT, 0);
    gl.disable(gl.POLYGON_OFFSET_FILL);

    if (state.showMesh) {
      gl.useProgram(renderer.lineProgram);
      gl.uniformMatrix4fv(renderer.lineVP, false, matrices.viewProjection);
      gl.uniform4fv(renderer.lineColor, state.activeCase && state.activeCase.flow === "helfrich"
        ? [1.0, 0.43, 0.42, 0.72]
        : [0.34, 0.92, 0.80, 0.67]);
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
      if (state.initialHoldRemaining > 0) {
        state.initialHoldRemaining = Math.max(0, state.initialHoldRemaining - elapsed);
      } else {
        state.progress += elapsed * state.speed / state.playDuration;
        if (state.progress > 1) {
          state.progress %= 1;
          state.initialHoldRemaining = state.activeCase ? (state.activeCase.holdSeconds || 0) : 0;
        }
        state.dirty = true;
      }
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
    if (state.playing && state.progress === 0 && state.initialHoldRemaining <= 0) {
      state.initialHoldRemaining = state.activeCase ? (state.activeCase.holdSeconds || 0) : 0;
    }
    state.lastTimestamp = 0;
    updatePlaybackUI();
    if (shouldAnnounce) announce(state.playing ? "动画继续" : "动画暂停");
  }

  function setProgress(progress, pause = false) {
    state.progress = clamp(progress, 0, 1);
    state.initialHoldRemaining = 0;
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
    const preset = state.activeCase && state.activeCase.camera ? state.activeCase.camera : { yaw: -0.72, pitch: 0.34, distance: 5.5 };
    state.camera.yaw = preset.yaw;
    state.camera.pitch = preset.pitch;
    state.camera.distance = preset.distance;
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
  densitySelect.addEventListener("change", () => {
    state.density = densitySelect.value;
    if (state.activeCase) loadCase(state.activeCase, false, true);
  });
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
    const isWillmore = state.activeCase.flow === "willmore";
    const isHelfrich = state.activeCase.flow === "helfrich";
    const isBendingFlow = isWillmore || isHelfrich;
    const computedSteps = diagnostics.computed_step_count || (data.frameCount - 1);
    const nominalTimeStep = Number(diagnostics.time_step);
    const startupFactor = Number(diagnostics.startup_factor || 1);
    const startupEnd = Number(diagnostics.startup_end_time || 0);
    const startupTimeStep = Number(diagnostics.startup_time_step || nominalTimeStep / startupFactor);
    const startupStatus = isWillmore && startupFactor > 1
      ? ` · 启动 δt=${startupTimeStep.toExponential(1)} 至 t=${startupEnd.toFixed(2)}`
      : "";
    solverStatus.textContent = `${data.vertexCount} 顶点 · ${data.triangleCount.toLocaleString()} 三角形 · 名义 τ=${nominalTimeStep.toExponential(0)}${startupStatus}`;
    verification.area.textContent = isBendingFlow
      ? (diagnostics.energy_monotone_saved_frames ? `${data.frameCount} 个保存状态弯曲能下降` : "弯曲能检查失败")
      : (diagnostics.surface_area_monotone ? `${computedSteps} 步表面积全部下降` : "表面积检查失败");
    verification.orientation.textContent = diagnostics.orientation_preserved ? `亏格 g=${diagnostics.genus} · 无退化` : "检测到网格退化";
    const volumeChange = isBendingFlow ? diagnostics.maximum_relative_volume_change : diagnostics.max_relative_volume_drift;
    const areaChange = diagnostics.maximum_relative_area_change || 0;
    verification.volume.textContent = isHelfrich
      ? `面积 / 体积最大变化 ${(areaChange * 100).toFixed(3)}% / ${(volumeChange * 100).toFixed(3)}%`
      : `${isWillmore ? "最大体积变化" : "最大体积漂移"} ${(volumeChange * 100).toFixed(3)}%`;
    energyCheckNote.innerHTML = isBendingFlow
      ? `保存的 ${data.frameCount} 个数值状态中，离散 Willmore 能从 ${diagnostics.initial_energy.toFixed(3)} 降至 ${diagnostics.final_energy.toFixed(3)}。`
      : "每一步验证 <i>W</i><sup>m+1</sup> + τ‖∇<sub>S</sub><i>H</i><sup>m+1</sup>‖² ≤ <i>W</i><sup>m</sup>。";
    volumeCheckNote.textContent = isHelfrich
      ? "每一步用两个全局乘子约束面积与体积的一阶变化；页面显示全离散时间步留下的实际误差。"
      : (isWillmore
        ? "无约束 Willmore 能具有尺度不变性，并不保持体积；这里如实显示相对体积变化。"
        : "页面显示实际体积漂移；精确保体积需要 Bao–Zhao 2021 的半隐式法向。");
    topologyNote.textContent = `${data.triangleCount.toLocaleString()} 个三角形在 ${data.frameCount} 个状态中保持同一连通关系；Euler 示性数 χ=${diagnostics.euler_characteristic}，未执行重网格。`;
    canvas.dataset.renderer = "webgl2";
    canvas.dataset.scheme = isHelfrich ? "constrained-relaxed-mdr-pfem-helfrich" : (isWillmore ? "relaxed-mdr-pfem-willmore" : "bgn-pfem-surface-diffusion");
    canvas.dataset.case = state.activeCase.slug;
    canvas.dataset.meshDensity = state.density;
    canvas.dataset.genus = String(diagnostics.genus);
    canvas.dataset.vertexCount = String(data.vertexCount);
    canvas.dataset.triangleCount = String(data.triangleCount);
    canvas.dataset.frameCount = String(data.frameCount);
    canvas.dataset.timeStep = String(nominalTimeStep);
    canvas.dataset.computedStepCount = String(computedSteps);
    canvas.dataset.startupFactor = String(startupFactor);
    canvas.dataset.startupTimeStep = String(startupTimeStep);
    canvas.dataset.startupEndTime = String(startupEnd);
    canvas.dataset.surfaceAreaMonotone = String(Boolean(diagnostics.surface_area_monotone));
    canvas.dataset.energyMonotone = String(isBendingFlow ? diagnostics.energy_monotone_saved_frames : diagnostics.surface_area_monotone);
    canvas.dataset.energyInequalitySatisfied = String(isBendingFlow
      ? Boolean(diagnostics.energy_monotone_saved_frames)
      : Boolean(diagnostics.energy_inequality_satisfied));
    canvas.dataset.orientationPreserved = String(diagnostics.orientation_preserved);
    canvas.dataset.maximumAreaIncrease = String(diagnostics.max_area_increase || 0);
    canvas.dataset.maximumVolumeDrift = String(volumeChange);
    canvas.dataset.maximumAreaDrift = String(areaChange);
    canvas.dataset.minimumTriangleQuality = String(diagnostics.minimum_triangle_quality);
  }

  function renderCaseButtons() {
    caseButtons.replaceChildren();
    for (const item of state.manifest.cases) {
      const button = document.createElement("button");
      button.type = "button";
      button.dataset.case = item.slug;
      button.textContent = item.shortName;
      button.setAttribute("aria-pressed", "false");
      button.addEventListener("click", () => loadCase(item));
      caseButtons.append(button);
    }
  }

  function updateCaseUI() {
    const item = state.activeCase;
    activeCaseTitle.textContent = item.name;
    algorithmTitle.textContent = `${item.name} · 完整算法`;
    for (const detail of algorithmDetails) detail.hidden = detail.dataset.algorithm !== item.slug;
    caseCaption.textContent = item.caption;
    caseSourceNote.textContent = `${item.sourceNote}${state.density === "fine" ? " · 原三角形共享边中点 1→4 剖分" : " · 原网格"}`;
    densitySelect.value = state.density;
    const availableVariants = item.variants || { standard: true };
    for (const option of densitySelect.options) option.disabled = !availableVariants[option.value];
    densitySelect.disabled = false;
    if (item.flow === "helfrich") {
      equationBody.classList.add("is-willmore");
      flowEyebrow.textContent = "CONSTRAINED RELAXED-MDR · HELFRICH FLOW";
      equationTag.textContent = "AREA + VOLUME";
      equationFirst.innerHTML = "<i>E</i> = ½∫<sub>Γ</sub> (<i>H</i> − κ̄)²";
      equationSecond.innerHTML = "d<i>A</i>/d<i>t</i> = 0 · d<i>V</i>/d<i>t</i> = 0";
      equationNote.textContent = "两个全局乘子约束面积和体积；弯曲能下降把扁椭球推向双凹红细胞形。";
      energyMetricLabel.innerHTML = "Helfrich 能 <i>E/E₀</i>";
      volumeMetricLabel.textContent = "面积 / 体积误差";
      energyLegend.textContent = "弯曲能";
      volumeLegend.textContent = "体积（金）· 面积（红）";
    } else if (item.flow === "willmore") {
      equationBody.classList.add("is-willmore");
      flowEyebrow.textContent = "RELAXED-MDR · PARAMETRIC FEM · WILLMORE FLOW";
      equationTag.textContent = "L² GRADIENT";
      equationFirst.innerHTML = "<i>V</i> = −Δ<sub>S</sub><i>H</i> − <i>H</i>|∇<sub>S</sub><b>ν</b>|² + ½<i>H</i>³";
      equationSecond.innerHTML = "<i>E</i> = ½∫<sub>Γ</sub> <i>H</i>²";
      equationNote.textContent = "Willmore 法向速度降低弯曲能；relaxed-MDR 独立选择切向网格速度。";
      energyMetricLabel.innerHTML = "Willmore 能 <i>E/E₀</i>";
      volumeMetricLabel.textContent = "体积变化";
      energyLegend.textContent = "弯曲能";
      volumeLegend.textContent = "体积变化";
    } else {
      equationBody.classList.remove("is-willmore");
      flowEyebrow.textContent = "BGN · PARAMETRIC FEM · SURFACE DIFFUSION";
      equationTag.textContent = "H⁻¹ GRADIENT";
      equationFirst.innerHTML = "<i>V</i> = −Δ<sub>S</sub><i>H</i>";
      equationSecond.innerHTML = "<i>H</i><b>n</b> = Δ<sub>S</sub> id";
      equationNote.textContent = "法向速度决定几何演化；弱形式自动产生切向网格运动。";
      energyMetricLabel.innerHTML = "表面积 <i>W/W₀</i>";
      volumeMetricLabel.textContent = "体积误差";
      energyLegend.textContent = "面积";
      volumeLegend.textContent = "体积误差";
    }
    for (const button of caseButtons.querySelectorAll("button")) {
      button.disabled = false;
      button.setAttribute("aria-pressed", String(button.dataset.case === item.slug));
    }
  }

  async function loadCase(item, initial = false, force = false) {
    if (!item || (!initial && !force && state.activeCase && state.activeCase.slug === item.slug)) return;
    const variants = item.variants || { standard: { trajectory: item.trajectory, diagnostics: item.diagnostics, bytes: item.bytes } };
    if (!variants[state.density]) state.density = variants.standard ? "standard" : Object.keys(variants)[0];
    const variant = variants[state.density];
    const serial = ++state.loadSerial;
    for (const button of caseButtons.querySelectorAll("button")) button.disabled = true;
    densitySelect.disabled = true;
    loadingPanel.hidden = false;
    loadingPanel.classList.remove("is-hidden");
    errorPanel.hidden = true;
    loadingText.textContent = `载入「${item.shortName}」${state.density === "fine" ? "三角形 1→4" : "原"}网格与 ${Math.max(1, Math.round(variant.bytes / 1048576))} MB 轨迹…`;
    try {
      const [buffer, diagnosticsResponse] = await Promise.all([fetchTrajectoryBuffer(variant), fetch(versionedAsset(variant.diagnostics))]);
      if (!diagnosticsResponse.ok) throw new Error(`诊断数据载入失败（HTTP ${diagnosticsResponse.status}）`);
      const diagnostics = await diagnosticsResponse.json();
      if (serial !== state.loadSerial) return;
      disposeRenderer();
      const parsedTrajectory = parseTrajectory(buffer);
      state.trajectory = variant.refine ? refineTrajectoryForDisplay(parsedTrajectory) : parsedTrajectory;
      state.diagnostics = diagnostics;
      state.activeCase = item;
      state.activeVariant = variant;
      state.renderer = createRenderer(state.gl, state.trajectory);
      const loadUrl = new URL(window.location.href);
      const hasRequestedProgress = initial && loadUrl.searchParams.has("t");
      const requestedProgress = hasRequestedProgress ? Number(loadUrl.searchParams.get("t")) : 0;
      state.progress = Number.isFinite(requestedProgress) ? clamp(requestedProgress, 0, 1) : 0;
      state.playDuration = item.playDuration || 12;
      state.initialHoldRemaining = state.progress === 0 ? (item.holdSeconds || 0) : 0;
      if (hasRequestedProgress) state.playing = false;
      resetCamera();
      updateCaseUI();
      installDiagnostics();
      resize();
      updatePlaybackUI();
      render();
      loadingPanel.classList.add("is-hidden");
      window.setTimeout(() => { loadingPanel.hidden = true; }, 450);
      const url = new URL(window.location.href);
      url.searchParams.set("case", item.slug);
      if (state.density === "fine") url.searchParams.set("mesh", "fine"); else url.searchParams.delete("mesh");
      if (!initial) url.searchParams.delete("t");
      window.history.replaceState({}, "", url);
      announce(`${item.shortName}的参数有限元轨迹已载入`);
    } catch (error) {
      if (serial !== state.loadSerial) return;
      loadingPanel.hidden = true;
      errorPanel.hidden = false;
      errorPanel.textContent = `无法启动可视化：${error.message}`;
      solverStatus.textContent = "载入失败";
      for (const button of caseButtons.querySelectorAll("button")) button.disabled = false;
      densitySelect.disabled = false;
      console.error(error);
    }
  }

  async function initialise() {
    try {
      loadingText.textContent = "读取曲面扩散案例清单…";
      const manifestResponse = await fetch(versionedAsset("trajectories/manifest.json"));
      if (!manifestResponse.ok) throw new Error(`案例清单载入失败（HTTP ${manifestResponse.status}）`);
      state.manifest = await manifestResponse.json();
      renderCaseButtons();
      const gl = canvas.getContext("webgl2", { antialias: true, alpha: true, depth: true, powerPreference: "high-performance" });
      if (!gl) throw new Error("当前浏览器或设备没有可用的 WebGL 2 上下文");
      state.gl = gl;
      const requested = new URL(window.location.href).searchParams.get("case");
      state.density = new URL(window.location.href).searchParams.get("mesh") === "fine" ? "fine" : "standard";
      const item = state.manifest.cases.find((candidate) => candidate.slug === requested)
        || state.manifest.cases.find((candidate) => candidate.slug === state.manifest.default)
        || state.manifest.cases[0];
      await loadCase(item, true);
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
