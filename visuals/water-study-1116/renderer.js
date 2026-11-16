import { createTerrain } from './terrain.js';
import { createBoat } from './boat.js';
import { createRipples } from './ripples.js';
import { backgroundHeight, makeWaterGrid, makeCrestGrid } from './water-surface.js';
import {
  fullVertex, skyFragment, displayFragment, shadowVertex, shadowFragment, crestShadowVertex,
  terrainVertex, terrainFragment, waterVertex, waterFragment
} from './shaders.js';

const toRadians = Math.PI / 180;
const unit = a => {
  const length = Math.hypot(...a) || 1;
  return a.map(n => n / length);
};
const cross = (a, b) => [
  a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]
];
const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const identity = new Float32Array([1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]);

export function cameraBasis(yaw, pitch) {
  const forward = [Math.sin(yaw) * Math.cos(pitch), Math.sin(pitch), Math.cos(yaw) * Math.cos(pitch)];
  const right = unit(cross(forward, [0, 1, 0]));
  return { forward, right, up: cross(right, forward) };
}

function look(eye, forward, right, up) {
  return new Float32Array([
    right[0], up[0], -forward[0], 0,
    right[1], up[1], -forward[1], 0,
    right[2], up[2], -forward[2], 0,
    -dot(right, eye), -dot(up, eye), dot(forward, eye), 1
  ]);
}

function multiply(a, b) {
  const out = new Float32Array(16);
  for (let col = 0; col < 4; col++) {
    for (let row = 0; row < 4; row++) {
      out[col * 4 + row] = a[row] * b[col * 4] + a[row + 4] * b[col * 4 + 1]
        + a[row + 8] * b[col * 4 + 2] + a[row + 12] * b[col * 4 + 3];
    }
  }
  return out;
}

function perspective(lens, aspect, near, far) {
  return new Float32Array([
    1 / (lens * aspect), 0, 0, 0, 0, 1 / lens, 0, 0,
    0, 0, (far + near) / (near - far), -1, 0, 0, (2 * far * near) / (near - far), 0
  ]);
}

function inverseViewProjection(eye, forward, right, up, lens, aspect, near, far) {
  // The camera basis and infinite perspective structure give the inverse directly.
  const k = (near - far) / (2 * far * near);
  const q = (near + far) / (2 * far * near);
  return new Float32Array([
    right[0] * lens * aspect, right[1] * lens * aspect, right[2] * lens * aspect, 0,
    up[0] * lens, up[1] * lens, up[2] * lens, 0,
    eye[0] * k, eye[1] * k, eye[2] * k, k,
    forward[0] + eye[0] * q, forward[1] + eye[1] * q, forward[2] + eye[2] * q, q
  ]);
}

function buildProgram(gl, vertex, fragment) {
  const program = gl.createProgram();
  for (const [kind, source] of [[gl.VERTEX_SHADER, vertex], [gl.FRAGMENT_SHADER, fragment]]) {
    const shader = gl.createShader(kind);
    gl.shaderSource(shader, source);
    gl.compileShader(shader);
    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      throw new Error(gl.getShaderInfoLog(shader));
    }
    gl.attachShader(program, shader);
    gl.deleteShader(shader);
  }
  gl.linkProgram(program);
  if (!gl.getProgramParameter(program, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(program));
  const uniforms = new Map();
  return {
    use() { gl.useProgram(program); },
    set(name, value) {
      if (!uniforms.has(name)) uniforms.set(name, gl.getUniformLocation(program, name));
      const uniform = uniforms.get(name);
      if (uniform === null) return;
      if (typeof value === 'number') gl.uniform1f(uniform, value);
      else if (value.length === 16) gl.uniformMatrix4fv(uniform, false, value);
      else if (value.length === 3) gl.uniform3fv(uniform, value);
      else gl.uniform2fv(uniform, value);
    },
    int(name, value) {
      if (!uniforms.has(name)) uniforms.set(name, gl.getUniformLocation(program, name));
      const uniform = uniforms.get(name);
      if (uniform !== null) gl.uniform1i(uniform, value);
    }
  };
}

function mesh(gl, data, flat = false) {
  const vao = gl.createVertexArray();
  const points = gl.createBuffer();
  const elements = gl.createBuffer();
  gl.bindVertexArray(vao);
  gl.bindBuffer(gl.ARRAY_BUFFER, points);
  gl.bufferData(gl.ARRAY_BUFFER, data.vertices, gl.STATIC_DRAW);
  const stride = flat ? 8 : 32;
  gl.enableVertexAttribArray(0);
  gl.vertexAttribPointer(0, flat ? 2 : 3, gl.FLOAT, false, stride, 0);
  if (!flat) {
    gl.enableVertexAttribArray(1);
    gl.vertexAttribPointer(1, 3, gl.FLOAT, false, stride, 12);
    gl.enableVertexAttribArray(2);
    gl.vertexAttribPointer(2, 2, gl.FLOAT, false, stride, 24);
  }
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, elements);
  gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, data.indices, gl.STATIC_DRAW);
  return () => {
    gl.bindVertexArray(vao);
    gl.drawElements(gl.TRIANGLES, data.indices.length, gl.UNSIGNED_INT, 0);
  };
}

function targetTexture(gl, width, height, internal, format, type, filter) {
  const texture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, texture);
  gl.texImage2D(gl.TEXTURE_2D, 0, internal, width, height, 0, format, type, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, filter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, filter);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  return texture;
}

function makeTarget(gl, width, height, hdr, depthOnly = false) {
  const framebuffer = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER, framebuffer);
  const depth = targetTexture(gl, width, height, gl.DEPTH_COMPONENT24, gl.DEPTH_COMPONENT, gl.UNSIGNED_INT, gl.NEAREST);
  gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.TEXTURE_2D, depth, 0);
  let color;
  if (!depthOnly) {
    color = targetTexture(gl, width, height, hdr ? gl.RGBA16F : gl.RGBA8, gl.RGBA,
      hdr ? gl.HALF_FLOAT : gl.UNSIGNED_BYTE, gl.LINEAR);
    gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, color, 0);
  } else {
    gl.drawBuffers([gl.NONE]);
    gl.readBuffer(gl.NONE);
  }
  if (gl.checkFramebufferStatus(gl.FRAMEBUFFER) !== gl.FRAMEBUFFER_COMPLETE) {
    gl.deleteFramebuffer(framebuffer);
    gl.deleteTexture(color);
    gl.deleteTexture(depth);
    return undefined;
  }
  return { framebuffer, depth, color, width, height };
}

function obstacleMask(ripples, obstacles) {
  const { resolution, size } = ripples;
  const mask = new Uint8Array(resolution * resolution);
  for (const { x, z, rx, rz } of obstacles) {
    const x0 = Math.max(0, Math.floor(((x - rx) / size + 0.5) * resolution));
    const x1 = Math.min(resolution, Math.ceil(((x + rx) / size + 0.5) * resolution));
    const z0 = Math.max(0, Math.floor(((z - rz) / size + 0.5) * resolution));
    const z1 = Math.min(resolution, Math.ceil(((z + rz) / size + 0.5) * resolution));
    for (let iz = z0; iz < z1; iz++) {
      const dz = ((iz + 0.5) / resolution * size - size / 2 - z) / rz;
      for (let ix = x0; ix < x1; ix++) {
        const dx = ((ix + 0.5) / resolution * size - size / 2 - x) / rx;
        if (dx * dx + dz * dz < 1) mask[iz * resolution + ix] = 255;
      }
    }
  }
  return mask;
}

function boatPose(state) {
  const { time, drifting, setting, wind } = state;
  const t = drifting ? state.boatTime : 0;
  const x = (setting === 1 ? -1.8 : 2.25) + 1.1 * Math.sin(t * 0.24);
  const z = 3.35 + 1.96 * Math.sin(t * 0.17);
  const bob = 0.038 * Math.sin(time * 2.84);
  const h = backgroundHeight(x, z, time, wind) * 0.60 + bob - 0.16;
  const theta = 1.00 + 0.36 * Math.sin(t * 0.28);
  const c = Math.cos(theta);
  const s = Math.sin(theta);
  const rocking = Math.sin(time * 2.2) * 0.05;
  return {
    matrix: new Float32Array([c, rocking, -s, 0, -rocking * c, 1, rocking * s, 0,
      s, 0, c, 0, x, h, z, 1]),
    wake: [x - s, z - c]
  };
}

export function makeRenderer(canvas) {
  const gl = canvas.getContext('webgl2', {
    alpha: false, antialias: false, depth: true, powerPreference: 'high-performance'
  });
  if (!gl) throw new Error('WebGL 2 unavailable');
  const hdr = !!gl.getExtension('EXT_color_buffer_float');
  const drawEmpty = gl.createVertexArray();
  const sky = buildProgram(gl, fullVertex, skyFragment);
  const display = buildProgram(gl, fullVertex, displayFragment);
  const terrain = buildProgram(gl, terrainVertex, terrainFragment);
  const shadow = buildProgram(gl, shadowVertex, shadowFragment);
  const crestShadow = buildProgram(gl, crestShadowVertex, shadowFragment);
  const water = buildProgram(gl, waterVertex, waterFragment);
  const terrainData = createTerrain('rockpool');
  const drawLagoon = mesh(gl, terrainData);
  const drawStage = mesh(gl, createTerrain('wave'));
  const drawBoat = mesh(gl, createBoat());
  const drawWater = mesh(gl, makeWaterGrid(), true);
  const drawCrest = mesh(gl, makeCrestGrid(), true);
  const ripples = createRipples(gl);
  ripples.setObstacleMask(obstacleMask(ripples, terrainData.obstacles ?? []));
  const shadowMap = makeTarget(gl, 1536, 1536, false, true);
  if (!shadowMap) throw new Error('Shadow framebuffer unavailable');
  let opaque;
  let scale = 1;
  let fpsEstimate = 16.7;
  let frameCounter = 0;
  let lastShadow = '';
  let lastWake = -10;

  function resize(dt) {
    if (dt > 0.002 && dt < 0.32) {
      fpsEstimate += (dt * 1000 - fpsEstimate) * 0.073;
      if (++frameCounter >= 24) {
        if (fpsEstimate > 38) scale = Math.max(0.60, scale * 0.84);
        else if (fpsEstimate < 23) scale = Math.min(1, scale * 1.085);
        frameCounter = 0;
      }
    }
    const ratio = Math.min(window.devicePixelRatio || 1, 1.35);
    const width = canvas.clientWidth * ratio;
    const height = canvas.clientHeight * ratio;
    const limit = Math.min(1, Math.sqrt(1020000 / Math.max(1, width * height)));
    const w = Math.max(1, Math.round(width * limit * scale));
    const h = Math.max(1, Math.round(height * limit * scale));
    if (opaque && opaque.width === w && opaque.height === h) return;
    canvas.width = w;
    canvas.height = h;
    if (opaque) {
      gl.deleteFramebuffer(opaque.framebuffer);
      gl.deleteTexture(opaque.color);
      gl.deleteTexture(opaque.depth);
    }
    opaque = makeTarget(gl, w, h, hdr) ?? makeTarget(gl, w, h, false);
    if (!opaque) throw new Error('Scene framebuffer unavailable');
  }

  function bind(program, uniform, index, texture) {
    gl.activeTexture(gl.TEXTURE0 + index);
    gl.bindTexture(gl.TEXTURE_2D, texture);
    program.int(uniform, index);
  }

  function setup(program, state, sun, sunlight, shadowMatrix) {
    program.use();
    program.int('uSetting', state.setting);
    program.set('uEye', state.eye);
    program.set('uSun', sun);
    program.set('uLight', sunlight);
    program.set('uViewport', [opaque.width, opaque.height]);
    program.set('uWind', state.wind);
    program.set('uTime', state.time);
    program.set('uClarity', state.clarity);
    program.set('uRippleSize', ripples.size);
    program.set('uRippleTexel', 1 / ripples.resolution);
    program.set('uWaveShape', 1);
    program.set('uWaveAmount', 1);
    program.set('uSunMatrix', shadowMatrix);
    bind(program, 'uShadow', 2, shadowMap.depth);
    bind(program, 'uRipple', 3, ripples.texture);
  }

  function draw(state, delta) {
    const waveSetting = state.setting === 2;
    if (state.time < lastWake) lastWake = -10;
    const haveBoat = !waveSetting && state.boat;
    const boat = haveBoat ? boatPose(state) : null;
    if (haveBoat && state.drifting && state.time - lastWake > 0.27) {
      ripples.disturb(...boat.wake, 0.22, 0.49);
      lastWake = state.time;
    }
    if (!waveSetting) ripples.step(delta);
    resize(delta);
    const { eye, yaw, pitch } = state;
    const { forward, right, up } = cameraBasis(yaw, pitch);
    const lens = Math.tan(state.fov * toRadians / 2);
    const aspect = opaque.width / opaque.height;
    const near = 0.075;
    const far = 135;
    const vp = multiply(perspective(lens, aspect, near, far), look(eye, forward, right, up));
    const inv = inverseViewProjection(eye, forward, right, up, lens, aspect, near, far);
    const altitude = state.altitude * toRadians;
    const azimuth = state.azimuth * toRadians;
    const sun = [Math.cos(altitude) * Math.sin(azimuth), Math.sin(altitude), Math.cos(altitude) * Math.cos(azimuth)];
    const warmth = 1 - Math.min(1, state.altitude / 37);
    const sunlight = [state.light * (1.01 + 0.10 * warmth), state.light * (0.96 - 0.15 * warmth),
      state.light * (0.87 - 0.32 * warmth)];
    const sunForward = sun.map(value => -value);
    const sunRight = unit(cross(sunForward, [0, 1, 0]));
    const sunUp = cross(sunRight, sunForward);
    const radius = waveSetting ? 16 : 32;
    const sunEye = sun.map((n, i) => n * 32 + (i === 2 ? 1.8 : 0));
    const sunView = look(sunEye, sunForward, sunRight, sunUp);
    const ortho = new Float32Array([1/radius,0,0,0, 0,1/radius,0,0, 0,0,-2/76,0, 0,0,-1,1]);
    const sunMatrix = multiply(ortho, sunView);
    const drawLand = waveSetting ? drawStage : drawLagoon;
    const shadowKey = [waveSetting, state.altitude, state.azimuth, haveBoat,
      haveBoat || waveSetting ? Math.floor(state.time * 17) : 0].join(',');
    if (shadowKey !== lastShadow) {
      gl.bindFramebuffer(gl.FRAMEBUFFER, shadowMap.framebuffer);
      gl.viewport(0, 0, shadowMap.width, shadowMap.height);
      gl.enable(gl.DEPTH_TEST);
      gl.depthMask(true);
      gl.clear(gl.DEPTH_BUFFER_BIT);
      shadow.use();
      shadow.set('uSunMatrix', sunMatrix);
      shadow.set('uModel', identity);
      drawLand();
      if (boat) {
        shadow.set('uModel', boat.matrix);
        drawBoat();
      }
      if (waveSetting) {
        crestShadow.use();
        crestShadow.set('uSunMatrix', sunMatrix);
        crestShadow.set('uTime', state.time);
        crestShadow.set('uWaveShape', 1);
        crestShadow.set('uWaveAmount', 1);
        drawCrest();
      }
      lastShadow = shadowKey;
    }

    gl.bindFramebuffer(gl.FRAMEBUFFER, opaque.framebuffer);
    gl.viewport(0, 0, opaque.width, opaque.height);
    gl.clear(gl.DEPTH_BUFFER_BIT);
    gl.disable(gl.DEPTH_TEST);
    setup(sky, state, sun, sunlight, sunMatrix);
    sky.set('uForward', forward);
    sky.set('uRight', right);
    sky.set('uUp', up);
    sky.set('uLens', lens);
    gl.bindVertexArray(drawEmpty);
    gl.drawArrays(gl.TRIANGLES, 0, 3);

    gl.enable(gl.DEPTH_TEST);
    setup(terrain, state, sun, sunlight, sunMatrix);
    terrain.set('uModel', identity);
    terrain.set('uViewProjection', vp);
    terrain.int('uCaustics', state.caustics && !waveSetting);
    drawLand();
    if (boat) {
      terrain.set('uModel', boat.matrix);
      drawBoat();
    }

    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
    gl.viewport(0, 0, opaque.width, opaque.height);
    gl.disable(gl.DEPTH_TEST);
    display.use();
    bind(display, 'uColor', 0, opaque.color);
    gl.bindVertexArray(drawEmpty);
    gl.drawArrays(gl.TRIANGLES, 0, 3);

    gl.clear(gl.DEPTH_BUFFER_BIT);
    gl.enable(gl.DEPTH_TEST);
    setup(water, state, sun, sunlight, sunMatrix);
    water.set('uViewProjection', vp);
    water.set('uInverseViewProjection', inv);
    water.set('uRoughness', state.roughness);
    water.int('uViewMode', state.viewMode);
    bind(water, 'uColor', 0, opaque.color);
    bind(water, 'uDepth', 1, opaque.depth);
    if (waveSetting) drawCrest(); else drawWater();
  }

  return {
    draw,
    disturb: (x, z, strength, radius) => ripples.disturb(x, z, strength, radius),
    resetRipples: () => {
      lastWake = -10;
      lastShadow = '';
      ripples.reset();
    }
  };
}
