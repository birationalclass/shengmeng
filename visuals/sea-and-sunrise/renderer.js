import { skySource } from './sky.js';
import { seaSource } from './sea.js';

const vertex = `
attribute vec2 position;
void main() {
  gl_Position = vec4(position, 0.0, 1.0);
}
`;

const fragment = `
precision highp float;

uniform vec2 uResolution;
uniform sampler2D uNoise;
uniform float uClock, uWind, uWave, uGrid, uCloud;
uniform float uStage, uBuild, uSky, uBands, uSun, uSea, uTrace;
uniform float uYaw, uPitch, uElevation, uScene;

${skySource}
${seaSource}

vec3 colorStudy(vec2 uv) {
  vec2 p = gl_FragCoord.xy - uResolution * 0.5;
  float pixel = 1.0 - step(mix(4.0, max(uResolution.x, uResolution.y), smoothstep(0.23, 0.57, uBuild)),
    max(abs(p.x), abs(p.y)));
  vec3 palette = mix(vec3(1.0, 0.32, 0.10), vec3(0.30), smoothstep(0.26, 0.55, uBuild));
  float swatch = smoothstep(0.58, 0.90, uBuild);
  if (uv.x < 0.43) palette = mix(palette, vec3(0.36, 0.22, 0.37), swatch);
  if (uv.x >= 0.43) palette = mix(palette, vec3(0.16, 0.15, 0.30), swatch);
  return mix(vec3(0.031, 0.025, 0.033), palette, pixel);
}

vec3 noiseStudy(vec3 color, vec2 screen) {
  float blend = smoothstep(0.015, 0.12, uBuild) * (1.0 - smoothstep(0.49, 0.73, uBuild));
  if (uStage != 4.0 || blend <= 0.0) return color;
  vec2 p = screen - vec2(0.03, 0.45);
  if (max(abs(p.x), abs(p.y)) > 0.23) return color;
  float sum = 0.0;
  float weight = 0.0;
  float amplitude = 0.5;
  p = p * 10.0 + 17.4;
  for (int i = 0; i < 5; i++) {
    float octave = smoothstep(0.03 + 0.073 * float(i), 0.14 + 0.073 * float(i), uBuild);
    sum += octave * amplitude * noise2(p);
    weight += octave * amplitude;
    amplitude *= 0.5;
    p = 2.0 * p + 17.0;
  }
  float sampleValue = clamp(0.5 + 1.6 * (sum / max(0.001, weight) - 0.5), 0.0, 1.0);
  return mix(color, vec3(sampleValue), blend);
}

void main() {
  vec2 uv = gl_FragCoord.xy / uResolution;
  vec2 screen = (2.0 * gl_FragCoord.xy - uResolution) / uResolution.y;
  vec3 color = vec3(0.017, 0.013, 0.021);

  if (uStage < 0.5) {
    color = colorStudy(uv);
  } else {
    float lens = min(0.80, 1.46 * uResolution.y / uResolution.x);
    float pitch = uPitch * lens / 0.80;
    vec3 forward = vec3(sin(uYaw) * cos(pitch), sin(pitch), cos(uYaw) * cos(pitch));
    vec3 right = vec3(cos(uYaw), 0.0, -sin(uYaw));
    vec3 up = cross(forward, right);
    vec3 ray = normalize(forward + lens * (screen.x * right + screen.y * up));
    float elevation = uScene == 2.0 ? 0.22 : uElevation;
    vec3 sun = normalize(vec3(0.0, sin(elevation), cos(elevation)));
    vec3 eye = vec3(0.0, 2.1, -3.0);

    if (ray.y >= 0.0) {
      color = atmosphere(ray, sun);
      if (uScene == 1.0) {
        color += stars(ray) + aurora(ray);
      } else {
        color = cloudscape(ray, sun, color);
        if (uScene == 2.0) {
          color = blackHole(color, ray, sun) + stars(ray) * 0.28;
        } else {
          color = sunDisk(color, ray, sun);
          if (uScene == 3.0) color = saturn(color, ray);
        }
      }
      color = mix(vec3(0.017, 0.013, 0.021), color, uSky);
    } else {
      if (uSea > 0.001) {
        vec3 horizon = atmosphere(normalize(vec3(ray.x, 0.0, ray.z)), sun);
        color = mix(color, seaColor(eye, ray, sun, horizon), uSea);
      }
      if (uTrace > 0.001) {
        float wave = 0.212 + 0.027 * sin((uv.x - 0.1) * 6.283 - uClock * 1.16);
        float line = 1.0 - smoothstep(0.0, 1.6 / uResolution.y, abs(uv.y - wave));
        color += vec3(0.76, 0.71, 0.64) * line * uTrace;
      }
    }
  }

  color = noiseStudy(color, screen);
  float vignette = 1.0 - 0.19 * dot((uv - 0.5), (uv - 0.5)) * 2.0;
  float grain = texture2D(uNoise, gl_FragCoord.xy / 256.0).r - 0.5;
  color = 1.0 - exp(-max(vec3(0.0), color * 1.09 * vignette) * 1.37);
  color = pow(color, vec3(0.91)) + grain * 0.013;
  gl_FragColor = vec4(max(vec3(0.0), color), 1.0);
}
`;

const uniformNames = [
  'Clock', 'Wind', 'Wave', 'Grid', 'Cloud', 'Stage', 'Build', 'Sky', 'Bands',
  'Sun', 'Sea', 'Trace', 'Yaw', 'Pitch', 'Elevation', 'Scene'
];

function compile(gl, kind, source) {
  const shader = gl.createShader(kind);
  gl.shaderSource(shader, source);
  gl.compileShader(shader);
  if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
    const log = gl.getShaderInfoLog(shader);
    gl.deleteShader(shader);
    throw new Error(log);
  }
  return shader;
}

function makeNoiseTexture(gl) {
  // Seeded white noise. The shader interpolates this lattice and builds its own cloud shapes.
  const bytes = new Uint8Array(256 * 256);
  let seed = 0x82f91b5d;
  for (let i = 0; i < bytes.length; i++) {
    seed ^= seed << 13;
    seed ^= seed >>> 17;
    seed ^= seed << 5;
    bytes[i] = seed & 255;
  }
  const texture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, texture);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.LUMINANCE, 256, 256, 0, gl.LUMINANCE, gl.UNSIGNED_BYTE, bytes);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.REPEAT);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.REPEAT);
}

export function createRenderer(canvas) {
  const gl = canvas.getContext('webgl', {
    alpha: false,
    antialias: false,
    depth: false,
    stencil: false,
    powerPreference: 'high-performance'
  });
  if (!gl) throw new Error('WebGL unavailable');

  const program = gl.createProgram();
  const vertexShader = compile(gl, gl.VERTEX_SHADER, vertex);
  const fragmentShader = compile(gl, gl.FRAGMENT_SHADER, fragment);
  gl.attachShader(program, vertexShader);
  gl.attachShader(program, fragmentShader);
  gl.linkProgram(program);
  gl.deleteShader(vertexShader);
  gl.deleteShader(fragmentShader);
  if (!gl.getProgramParameter(program, gl.LINK_STATUS)) {
    throw new Error(gl.getProgramInfoLog(program));
  }
  gl.useProgram(program);

  const geometry = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, geometry);
  gl.bufferData(gl.ARRAY_BUFFER, new Float32Array([-1, -1, 3, -1, -1, 3]), gl.STATIC_DRAW);
  const position = gl.getAttribLocation(program, 'position');
  gl.enableVertexAttribArray(position);
  gl.vertexAttribPointer(position, 2, gl.FLOAT, false, 0, 0);

  makeNoiseTexture(gl);
  gl.uniform1i(gl.getUniformLocation(program, 'uNoise'), 0);
  const resolution = gl.getUniformLocation(program, 'uResolution');
  const uniforms = uniformNames.map(name => gl.getUniformLocation(program, 'u' + name));

  let scale = 1;
  let averageFrame = 16.7;
  let samples = 0;

  function resize() {
    const ratio = Math.min(window.devicePixelRatio || 1, 1.35);
    const width = canvas.clientWidth * ratio;
    const height = canvas.clientHeight * ratio;
    const limit = Math.min(1, Math.sqrt(1050000 / Math.max(1, width * height)));
    const w = Math.max(1, Math.round(width * limit * scale));
    const h = Math.max(1, Math.round(height * limit * scale));
    if (canvas.width === w && canvas.height === h) return;
    canvas.width = w;
    canvas.height = h;
    gl.viewport(0, 0, w, h);
    gl.uniform2f(resolution, w, h);
  }

  return function render(state, frameTime) {
    if (frameTime > 0 && frameTime < 400) {
      averageFrame += (frameTime - averageFrame) * 0.067;
      samples++;
      if (samples >= 24) {
        if (averageFrame > 27) scale = Math.max(0.52, scale * 0.85);
        if (averageFrame < 19) scale = Math.min(1, scale * 1.06);
        samples = 0;
      }
    }
    resize();
    for (let i = 0; i < uniforms.length; i++) {
      gl.uniform1f(uniforms[i], state[uniformNames[i]]);
    }
    gl.drawArrays(gl.TRIANGLES, 0, 3);
  };
}
