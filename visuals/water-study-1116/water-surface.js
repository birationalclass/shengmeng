// Independent WebGL surface model. The impulse field in ripples.js is
// superposed with a directional spectrum for wind-driven background motion.
const modes = Array.from({ length: 18 }, (_, i) => {
  const angle = 0.46 + Math.sin(i * 2.39996) * 1.65;
  const waveNumber = 1.12 * 1.249 ** i;
  const amplitude = 0.034 * 0.85 ** i;
  const phase = (i * i * 1.618 + 4.6 * i) % (2 * Math.PI);
  return [Math.cos(angle) * waveNumber, Math.sin(angle) * waveNumber,
    Math.sqrt(9.81 * waveNumber), amplitude, phase];
});

export function backgroundHeight(x, z, time, wind) {
  return modes.slice(0, 8).reduce((height, [kx, kz, frequency, amplitude, phase]) =>
    height + amplitude * Math.sin(kx * x + kz * z - time * frequency + phase) * wind, 0);
}

const term = (mode, lowHeight, highHeight) => {
  const [kx, kz, frequency, amplitude, phase] = mode.map(value => value.toFixed(7));
  return `
    phase = dot(p, vec2(${kx}, ${kz})) - ${frequency} * uTime + ${phase};
    ${lowHeight ? `height += ${amplitude} * sin(phase);` : ''}
    ${highHeight ? `slope += ${amplitude} * cos(phase) * vec2(${kx}, ${kz});` : ''}`;
};

export const surfaceSource = `
uniform sampler2D uRipple;
uniform float uTime;
uniform float uRippleSize;
uniform float uRippleTexel;
uniform float uWind;
uniform float uWaveShape;
uniform float uWaveAmount;

vec2 waveUV(vec2 position) {
  return position / uRippleSize + 0.5;
}

float impulse(vec2 position) {
  vec2 uv = waveUV(position);
  if (any(lessThan(uv, vec2(0.0))) || any(greaterThan(uv, vec2(1.0)))) return 0.0;
  return textureLod(uRipple, uv, 0.0).r;
}

float windHeight(vec2 p) {
  float phase;
  float height = 0.0;
  ${modes.slice(0, 8).map(mode => term(mode, true, false)).join('')}
  return height * uWind;
}

vec2 windSlope(vec2 p, float footprint) {
  float phase;
  vec2 slope = vec2(0.0);
  vec2 fine = vec2(0.0);
  ${modes.slice(0, 11).map(mode => term(mode, false, true)).join('')}
  fine = slope;
  slope = vec2(0.0);
  ${modes.slice(11).map(mode => term(mode, false, true)).join('')}
  return (fine + slope * (1.0 - smoothstep(0.016, 0.053, footprint))) * uWind;
}

vec2 waterSlope(vec2 p, float footprint) {
  float offset = max(0.12, uRippleTexel * uRippleSize * 0.60);
  vec2 dx = vec2(offset, 0.0);
  vec2 dz = vec2(0.0, offset);
  vec2 wave = vec2(impulse(p + dx) - impulse(p - dx), impulse(p + dz) - impulse(p - dz));
  return windSlope(p, footprint) + wave / (2.0 * offset);
}

// A broken wave sheet. V runs from the footprint to the overturning lip.
vec3 crestPosition(vec2 uv) {
  float x = uv.x;
  float v = uv.y;
  float edge = smoothstep(0.0, 0.31, 1.0 - abs(x));
  float section = sin(3.141593 * v);
  float stagger = edge * (0.041 * sin(8.8 * x + 0.3) + 0.021 * sin(17.4 * x));
  float turn = smoothstep(0.59, 0.99, v + stagger);
  float tip = smoothstep(0.77, 1.0, v + stagger);

  // Three unequal lobes share one face and then separate into the crest tips.
  vec3 peakOffset = x - vec3(-0.39, 0.035, 0.40);
  vec3 peaks = exp(-peakOffset * peakOffset * vec3(16.0, 52.0, 52.0));
  float ridge = edge * (0.48 + dot(peaks, vec3(1.36, 1.91, 2.41)));
  float lift = smoothstep(0.29, 0.88, v + stagger);
  float height = ridge * (lift - tip * (0.16 + 0.065 * sin(x * 14.0 - 1.6)));

  float frontWing = x - 0.70;
  float sideWing = x + 0.63;
  float apron = 0.45 * exp(-frontWing * frontWing * 23.0)
    + 0.23 * exp(-sideWing * sideWing * 31.0);
  float apronLift = smoothstep(0.0, 0.085, v) * (1.0 - smoothstep(0.13, 0.37, v));
  height += edge * (apron * apronLift + 0.19 * section * section);

  // Creases sweep diagonally toward the lip, with a finer ridged edge on top.
  float foldMask = edge * smoothstep(0.19, 0.41, v);
  float fold = sin(11.3 * x - 7.8 * v + 0.68 * sin(5.2 * x + 6.9 * v));
  float ruffle = sin(20.2 * x + 10.6 * v);
  float motion = sin(uTime * 1.8 + x * 7.4);
  height += foldMask * (0.12 * fold * section + tip * (0.061 * ruffle + 0.028 * motion));

  float front = -1.14 - edge * (0.85 + 0.84 * apron + 0.17 * cos(13.1 * x - 0.2));
  float back = 2.54 + edge * (0.28 * sin(x * 7.2) + 0.16 * cos(10.2 * x));
  float overhang = (1.58 + 0.43 * peaks.y + 0.49 * peaks.z + 0.13 * ruffle) * turn * edge;
  float crestZ = mix(front, back, v) - overhang
    + foldMask * (0.17 * fold * section + 0.05 * motion * tip);
  float width = 4.25 * (0.76 + 0.24 * section);
  float curlX = edge * (0.17 * sin(x * 5.5) * section + (0.18 + 0.15 * ruffle) * tip);
  return vec3(x * width + curlX * uWaveShape, -0.105 + height * uWaveAmount,
    mix(mix(front, back, v), crestZ, uWaveShape));
}
`;

function makeGrid(columns, rows, x0, x1, z0, z1) {
  const vertices = new Float32Array((columns + 1) * (rows + 1) * 2);
  const indices = new Uint32Array(columns * rows * 6);
  let vertexOffset = 0;
  let indexOffset = 0;
  for (let row = 0; row <= rows; row++) {
    for (let column = 0; column <= columns; column++) {
      vertices[vertexOffset++] = x0 + (x1 - x0) * column / columns;
      vertices[vertexOffset++] = z0 + (z1 - z0) * row / rows;
      if (column === columns || row === rows) continue;
      const first = row * (columns + 1) + column;
      const nextRow = first + columns + 1;
      indices.set([first, nextRow, first + 1, first + 1, nextRow, nextRow + 1], indexOffset);
      indexOffset += 6;
    }
  }
  return { vertices, indices };
}

export function makeWaterGrid() {
  return makeGrid(142, 142, -24, 24, -24, 24);
}

export function makeCrestGrid() {
  return makeGrid(192, 64, -1, 1, 0, 1);
}
