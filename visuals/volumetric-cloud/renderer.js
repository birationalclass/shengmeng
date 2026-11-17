import { generateVolumes } from './volume-noise.js';
import { fullVertex, marchFragment, historyFragment, skyFragment, compositeFragment } from './shaders.js';

const radians = Math.PI / 180;
const seaLevel = 0.018;
const earthRadius = 6371;
const qualityLevels = {
  auto: { scale: 0.51, steps: 70, lights: 4 },
  fast: { scale: 0.39, steps: 48, lights: 3 },
  high: { scale: 0.67, steps: 92, lights: 5 }
};

export function cameraBasis(yaw, pitch) {
  const forward = [Math.sin(yaw) * Math.cos(pitch), Math.sin(pitch), Math.cos(yaw) * Math.cos(pitch)];
  const right = [Math.cos(yaw), 0, -Math.sin(yaw)];
  const up = [-Math.sin(yaw) * Math.sin(pitch), Math.cos(pitch), -Math.cos(yaw) * Math.sin(pitch)];
  return { forward, right, up };
}

function localFrame(x, altitude, z) {
  const length = earthRadius + altitude;
  const horizontal = x * x + z * z;
  const radialY = Math.sqrt(length * length - horizontal);
  const eye = [x, altitude - horizontal / (length + radialY), z];
  const up = [x / length, radialY / length, z / length];
  const eastLength = Math.hypot(up[0], up[1]);
  const east = [up[1] / eastLength, -up[0] / eastLength, 0];
  const south = [east[1] * up[2], -east[0] * up[2], eastLength];
  const orient = direction => east.map((n, i) => n * direction[0] + up[i] * direction[1] + south[i] * direction[2]);
  return { eye, up, orient };
}

function buildProgram(gl, fragment) {
  const program = gl.createProgram();
  for (const [type, source] of [[gl.VERTEX_SHADER, fullVertex], [gl.FRAGMENT_SHADER, fragment]]) {
    const shader = gl.createShader(type);
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(shader));
    gl.attachShader(program, shader);
    gl.deleteShader(shader);
  }
  gl.linkProgram(program);
  if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(program));
  const uniforms = new Map();
  function location(name) {
    if (!uniforms.has(name)) uniforms.set(name, gl.getUniformLocation(program, name));
    return uniforms.get(name);
  }
  return {
    use: () => gl.useProgram(program),
    set(name, value) {
      const uniform = location(name);
      if (typeof value === 'number') gl.uniform1f(uniform, value);
      else if (value.length === 3) gl.uniform3fv(uniform, value);
      else gl.uniform2fv(uniform, value);
    },
    int(name, value) { gl.uniform1i(location(name), value); }
  };
}

async function getBitmap(name) {
  const response = await fetch(new URL(name, import.meta.url));
  if (!response.ok) throw new Error(name + ' ' + response.status);
  return createImageBitmap(await response.blob(), { imageOrientation: 'from-image',
    premultiplyAlpha: 'none', colorSpaceConversion: 'none' });
}

function allocate2D(gl, size, options) {
  const texture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, texture);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, options.repeat ? gl.REPEAT : gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, options.filter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, options.filter);
  if (options.bitmap) {
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, gl.RGBA, gl.UNSIGNED_BYTE, options.bitmap);
  } else {
    gl.texStorage2D(gl.TEXTURE_2D, 1, options.format, ...size);
  }
  return texture;
}

function allocate3D(gl, size, bytes) {
  const texture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_3D, texture);
  for (const axis of [gl.TEXTURE_WRAP_S, gl.TEXTURE_WRAP_T, gl.TEXTURE_WRAP_R]) {
    gl.texParameteri(gl.TEXTURE_3D, axis, gl.REPEAT);
  }
  gl.texParameteri(gl.TEXTURE_3D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_3D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texStorage3D(gl.TEXTURE_3D, 1, gl.RGBA8, size, size, size);
  gl.texSubImage3D(gl.TEXTURE_3D, 0, 0, 0, 0, size, size, size, gl.RGBA, gl.UNSIGNED_BYTE, bytes);
  return texture;
}

function target(gl, width, height, hdr, hasRange) {
  const fbo = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER, fbo);
  const color = allocate2D(gl, [width, height], {
    format: hdr ? gl.RGBA16F : gl.RGBA8, filter: gl.LINEAR, repeat: !hasRange
  });
  gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, color, 0);
  let range;
  if (hasRange) {
    range = allocate2D(gl, [width, height], { format: hdr ? gl.R16F : gl.R8, filter: gl.NEAREST });
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT1, gl.TEXTURE_2D, range, 0);
    gl.drawBuffers([gl.COLOR_ATTACHMENT0, gl.COLOR_ATTACHMENT1]);
  }
  if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) {
    throw new Error('体积云渲染缓冲区分配失败');
  }
  return { fbo, color, range, width, height };
}

function freeTarget(gl, buffer) {
  gl.deleteFramebuffer(buffer.fbo);
  gl.deleteTexture(buffer.color);
  gl.deleteTexture(buffer.range);
}

function directSun(altitude) {
  // Effective relative path lengths through the warm marine boundary layer.
  const s = Math.max(0.026, Math.sin(altitude));
  const airmass = 1 / (s + 0.12 * Math.exp(-s * 4));
  const brightness = 2.58 * (0.83 + 0.17 * Math.min(1, s * 3.2));
  return [0.025, 0.117, 0.27].map(k => brightness * Math.exp(-k * (airmass - 1)));
}

export async function createCloudRenderer(canvas, dataset = {}) {
  const gl = canvas.getContext('webgl2', {
    alpha: false, depth: false, stencil: false, antialias: false, powerPreference: 'high-performance'
  });
  if (!gl) throw new Error('当前浏览器或设备不支持 WebGL 2。');
  const floating = Boolean(gl.getExtension('EXT_color_buffer_float'));
  const weatherCache = new Map();
  let weatherGeneration = 0;
  async function loadWeather(data) {
    const lo = data.lowTexture ?? 'weather-lo.png';
    const hi = data.highTexture ?? 'weather-hi.png';
    if (!weatherCache.has(lo)) {
      const pending = Promise.all([getBitmap(lo), getBitmap(hi)]).then(bitmaps => bitmaps.map(bitmap => {
        const texture = allocate2D(gl, null, { bitmap, filter: gl.LINEAR });
        bitmap.close();
        return texture;
      }));
      weatherCache.set(lo, pending);
      pending.catch(() => weatherCache.delete(lo));
    }
    return weatherCache.get(lo);
  }
  let [weatherLo, weatherHi] = await loadWeather(dataset);
  const { shape, detail, shapeSize, detailSize } = generateVolumes();
  const shapeTexture = allocate3D(gl, shapeSize, shape);
  const detailTexture = allocate3D(gl, detailSize, detail);

  const marchProgram = buildProgram(gl, marchFragment);
  const historyProgram = buildProgram(gl, historyFragment);
  const atmosphereProgram = buildProgram(gl, skyFragment);
  const sceneProgram = buildProgram(gl, compositeFragment);
  gl.bindVertexArray(gl.createVertexArray());

  const atmosphere = target(gl, 224, 96, floating, false);
  const atmosphereScale = floating ? 1 : 2.5;
  let history = [];
  let current;
  let front = 0;
  let previousView;
  let wasQuality;
  let historyKey;
  let skyKey;
  let sequence = 0;
  let currentScale = 1;
  let frameAverage = 16.7;
  let observations = 0;

  function useTexture(program, name, unit, texture, type = gl.TEXTURE_2D) {
    gl.activeTexture(gl.TEXTURE0 + unit);
    gl.bindTexture(type, texture);
    program.int(name, unit);
  }

  function prepareProgram(program, info) {
    program.use();
    program.set('uEye', info.eye);
    program.set('uForward', info.forward);
    program.set('uRight', info.right);
    program.set('uUp', info.up);
    program.set('uLens', info.lens);
    program.set('uSun', info.sun);
    program.set('uLocalUp', info.localUp);
  }

  function setupCloud(program, state, info) {
    prepareProgram(program, info);
    program.set('uSunColor', info.sunColor);
    program.set('uWeatherSpan', state.span);
    program.set('uWindTime', state.time);
    program.set('uCoverage', state.coverage);
    program.set('uThickness', state.thickness);
    program.set('uDiffusion', state.diffusion);
    program.int('uCloudSteps', info.steps);
    program.int('uLightSteps', info.lights);
    program.int('uDebugCloud', state.debug);
    program.int('uLayers', state.layers);
    useTexture(program, 'uWeatherLo', 0, weatherLo);
    useTexture(program, 'uWeatherHi', 1, weatherHi);
    useTexture(program, 'uShape', 2, shapeTexture, gl.TEXTURE_3D);
    useTexture(program, 'uDetail', 3, detailTexture, gl.TEXTURE_3D);
  }

  function drawTo(buffer) {
    gl.bindFramebuffer(gl.FRAMEBUFFER, buffer?.fbo ?? null);
    gl.viewport(0, 0, buffer?.width ?? canvas.width, buffer?.height ?? canvas.height);
    gl.drawArrays(gl.TRIANGLES, 0, 3);
  }

  function resize(state, dt) {
    const { scale } = qualityLevels[state.quality];
    if (state.quality !== wasQuality) {
      wasQuality = state.quality;
      currentScale = 1;
      frameAverage = 16.7;
      observations = 0;
    }
    if (state.quality === 'auto' && dt > 5 && dt < 200) {
      frameAverage += (dt - frameAverage) * 0.065;
      if (++observations >= 26) {
        if (frameAverage > 33) currentScale = Math.max(0.61, currentScale * 0.83);
        if (frameAverage < 18) currentScale = Math.min(1, currentScale * 1.065);
        observations = 0;
      }
    }
    const ratio = Math.min(window.devicePixelRatio || 1, 1.30);
    let width = Math.max(4, Math.round(canvas.clientWidth * ratio));
    let height = Math.max(4, Math.round(canvas.clientHeight * ratio));
    const limit = Math.min(1, Math.sqrt(1500000 / (width * height)));
    width = Math.round(width * limit);
    height = Math.round(height * limit);
    if (canvas.width !== width || canvas.height !== height) {
      canvas.width = width;
      canvas.height = height;
      previousView = undefined;
    }
    const w = Math.max(4, Math.round(width * scale * currentScale));
    const h = Math.max(4, Math.round(height * scale * currentScale));
    if (current && current.width === w && current.height === h) return;
    if (current) {
      freeTarget(gl, current);
      for (const old of history) freeTarget(gl, old);
    }
    current = target(gl, w, h, floating, true);
    history = [target(gl, w, h, floating, true), target(gl, w, h, floating, true)];
    front = 0;
    previousView = undefined;
  }

  function draw(state, elapsed) {
    resize(state, elapsed);
    const basis = cameraBasis(state.yaw, state.pitch);
    const local = localFrame(state.x, Math.max(seaLevel, state.altitude), state.z);
    const altitude = state.solarAltitude * radians;
    const azimuth = state.solarAzimuth * radians;
    const sun = local.orient([Math.sin(azimuth) * Math.cos(altitude), Math.sin(altitude), Math.cos(azimuth) * Math.cos(altitude)]);
    const lensY = Math.tan(state.fov * radians / 2);
    const lensX = lensY * canvas.width / canvas.height;
    const info = {
      eye: local.eye,
      lens: [lensX, lensY],
      sun,
      sunColor: directSun(altitude),
      forward: local.orient(basis.forward),
      right: local.orient(basis.right),
      up: local.orient(basis.up),
      localUp: local.up,
      ...qualityLevels[state.quality]
    };
    const skyHeight = Math.round(state.altitude * 6) / 6;
    const nextSkyKey = [state.solarAltitude, skyHeight].join();
    if (nextSkyKey !== skyKey) {
      atmosphereProgram.use();
      atmosphereProgram.set('uSunAltitude', altitude);
      atmosphereProgram.set('uEyeAltitude', skyHeight);
      atmosphereProgram.set('uAtmosphereScale', atmosphereScale);
      drawTo(atmosphere);
      skyKey = nextSkyKey;
    }

    setupCloud(marchProgram, state, info);
    marchProgram.int('uFrame', sequence++ % 4096);
    marchProgram.set('uCloudRange', state.cloudRange ?? 50);
    drawTo(current);

    const nextHistoryKey = [state.solarAltitude, state.solarAzimuth, state.layers, state.cloudRange,
      state.coverage, state.thickness, state.diffusion, state.debug, state.quality].join();
    const before = previousView ?? info;
    const delta = Math.hypot(...before.eye.map((n, i) => n - info.eye[i]));
    const yawDelta = Math.hypot(...before.forward.map((n, i) => n - info.forward[i]));
    const allowHistory = previousView && historyKey === nextHistoryKey && delta < 7 && yawDelta < 0.55;
    prepareProgram(historyProgram, info);
    historyProgram.set('uPreviousEye', before.eye);
    historyProgram.set('uPreviousForward', before.forward);
    historyProgram.set('uPreviousRight', before.right);
    historyProgram.set('uPreviousUp', before.up);
    historyProgram.set('uPreviousLens', before.lens);
    const sameView = Boolean(allowHistory && delta < 0.0003 && yawDelta < 0.0002 &&
      Math.abs(info.lens[1] - before.lens[1]) < 0.0002);
    historyProgram.int('uSameView', sameView);
    historyProgram.set('uHistoryWeight', allowHistory ? Math.max(0.38, 0.87 - 0.14 * delta - 2.0 * yawDelta) : 0);
    useTexture(historyProgram, 'uCurrent', 0, current.color);
    useTexture(historyProgram, 'uCurrentRange', 1, current.range);
    useTexture(historyProgram, 'uPrevious', 2, history[front].color);
    useTexture(historyProgram, 'uPreviousRange', 3, history[front].range);
    const back = 1 - front;
    drawTo(history[back]);
    front = back;

    setupCloud(sceneProgram, state, info);
    const [islandX, islandZ] = state.island ?? [state.x + 100, state.z + 100];
    const island = localFrame(islandX, 0, islandZ).eye;
    sceneProgram.set('uIsland', island);
    sceneProgram.set('uIslandHeading', state.islandHeading ?? state.yaw);
    sceneProgram.set('uAtmosphereScale', atmosphereScale);
    sceneProgram.set('uExposure', state.exposure);
    sceneProgram.set('uTime', state.time);
    useTexture(sceneProgram, 'uFog', 4, history[front].color);
    useTexture(sceneProgram, 'uRange', 5, history[front].range);
    useTexture(sceneProgram, 'uSkyLUT', 6, atmosphere.color);
    drawTo();
    previousView = info;
    historyKey = nextHistoryKey;
  }

  return {
    draw,
    async setWeather(next) {
      const request = ++weatherGeneration;
      const pair = await loadWeather(next);
      if (request !== weatherGeneration) return false;
      [weatherLo, weatherHi] = pair;
      previousView = undefined;
      return true;
    }
  };
}
