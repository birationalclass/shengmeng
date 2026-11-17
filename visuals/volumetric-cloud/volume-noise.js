// Periodic density fields. Coherent gradient noise builds the low-frequency
// shape and three cellular frequencies give both the rounded lobes and erosion.

function hash(x, y, z, seed) {
  let n = Math.imul(x + seed, 0x7feb352d) ^ Math.imul(y + 37, 0x846ca68b) ^ Math.imul(z + 17, 0x4e67c6a7);
  n = Math.imul(n ^ (n >>> 16), 0x45d9f3b);
  n = Math.imul(n ^ (n >>> 16), 0x45d9f3b);
  return ((n ^ (n >>> 16)) >>> 0) / 4294967296;
}

const clamp = x => Math.max(0, Math.min(1, x));
const lerp = (a, b, x) => a + (b - a) * x;
const fade = x => x * x * x * (x * (x * 6 - 15) + 10);
const wrap = (i, n) => (i % n + n) % n;
const index = (x, y, z, n) => x + n * (y + n * z);

function gradientField(period, seed) {
  const directions = new Float32Array(period ** 3 * 3);
  for (let z = 0; z < period; z++) {
    for (let y = 0; y < period; y++) {
      for (let x = 0; x < period; x++) {
        const at = index(x, y, z, period) * 3;
        const phi = hash(x, y, z, seed) * 2 * Math.PI;
        const hz = 2 * hash(x, y, z, seed + 29) - 1;
        const projected = Math.sqrt(Math.max(0, 1 - hz * hz));
        directions[at] = Math.cos(phi) * projected;
        directions[at + 1] = Math.sin(phi) * projected;
        directions[at + 2] = hz;
      }
    }
  }
  return (x, y, z) => {
    x *= period;
    y *= period;
    z *= period;
    const ix = Math.floor(x);
    const iy = Math.floor(y);
    const iz = Math.floor(z);
    x -= ix;
    y -= iy;
    z -= iz;
    const fx = fade(x), fy = fade(y), fz = fade(z);
    let output = 0;
    for (let c = 0; c < 2; c++) {
      for (let b = 0; b < 2; b++) {
        for (let a = 0; a < 2; a++) {
          const at = index(wrap(ix + a, period), wrap(iy + b, period), wrap(iz + c, period), period) * 3;
          const d = directions[at] * (x - a) + directions[at + 1] * (y - b) + directions[at + 2] * (z - c);
          output += d * (a ? fx : 1 - fx) * (b ? fy : 1 - fy) * (c ? fz : 1 - fz);
        }
      }
    }
    return clamp(0.5 + 0.87 * output);
  };
}

function cellularField(period, seed) {
  const sites = new Float32Array(period ** 3 * 3);
  for (let z = 0; z < period; z++) {
    for (let y = 0; y < period; y++) {
      for (let x = 0; x < period; x++) {
        const at = 3 * index(x, y, z, period);
        sites[at] = 0.12 + 0.76 * hash(x, y, z, seed);
        sites[at + 1] = 0.12 + 0.76 * hash(x, y, z, seed + 19);
        sites[at + 2] = 0.12 + 0.76 * hash(x, y, z, seed + 47);
      }
    }
  }
  return (x, y, z) => {
    x *= period;
    y *= period;
    z *= period;
    const ix = Math.floor(x);
    const iy = Math.floor(y);
    const iz = Math.floor(z);
    const px = x - ix, py = y - iy, pz = z - iz;
    let nearest = 4;
    for (let c = -1; c <= 1; c++) {
      const nz = wrap(iz + c, period);
      for (let b = -1; b <= 1; b++) {
        const ny = wrap(iy + b, period);
        for (let a = -1; a <= 1; a++) {
          const at = index(wrap(ix + a, period), ny, nz, period) * 3;
          const dx = a + sites[at] - px;
          const dy = b + sites[at + 1] - py;
          const dz = c + sites[at + 2] - pz;
          nearest = Math.min(nearest, dx * dx + dy * dy + dz * dz);
        }
      }
    }
    return clamp(1 - Math.sqrt(nearest) * 0.93);
  };
}

export function generateVolumes() {
  const large = gradientField(4, 93);
  const small = gradientField(9, 17);
  const fine = gradientField(19, 31);
  const lobes = cellularField(5, 131);
  const shapes = cellularField(10, 71);
  const details = [cellularField(4, 23), cellularField(8, 54), cellularField(15, 91)];
  const shapeSize = 64;
  const detailSize = 32;
  const shape = new Uint8Array(shapeSize ** 3 * 4);
  const detail = new Uint8Array(detailSize ** 3 * 4);

  for (let z = 0; z < shapeSize; z++) {
    for (let y = 0; y < shapeSize; y++) {
      for (let x = 0; x < shapeSize; x++) {
        const a = x / shapeSize, b = y / shapeSize, c = z / shapeSize;
        const billow = lobes(a, b, c);
        const worley = shapes(a, b, c);
        const coherent = large(a, b, c) * 0.64 + small(a, b, c) * 0.28 + fine(a, b, c) * 0.08;
        const at = 4 * index(x, y, z, shapeSize);
        shape[at] = clamp(lerp(coherent, Math.max(coherent, billow), 0.38) * 1.3 - 0.12) * 255;
        shape[at + 1] = (billow * 0.70 + worley * 0.30) * 255;
        shape[at + 2] = fine(a, b, c) * 255;
        shape[at + 3] = 255;
      }
    }
  }
  for (let z = 0; z < detailSize; z++) {
    for (let y = 0; y < detailSize; y++) {
      for (let x = 0; x < detailSize; x++) {
        const at = 4 * index(x, y, z, detailSize);
        for (let channel = 0; channel < 3; channel++) {
          detail[at + channel] = details[channel](x / detailSize, y / detailSize, z / detailSize) * 255;
        }
        detail[at + 3] = 255;
      }
    }
  }
  return { shapeSize, detailSize, shape, detail };
}
