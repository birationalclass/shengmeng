const STRIDE = 8;
const ROCK = 0;
const SEABED = 1;
const STAGE = 2;
const BLOCK = 5;

const clamp = (value, low, high) => Math.max(low, Math.min(high, value));
const mix = (a, b, t) => a + (b - a) * t;
const ease = t => t * t * (3 - 2 * t);

function hash(x, y, z) {
  let h = Math.imul(x + 37, 374761393) ^ Math.imul(y - 13, 668265263) ^ Math.imul(z + 11, 2246822519);
  h = Math.imul(h ^ (h >>> 13), 1274126177);
  return ((h ^ (h >>> 16)) >>> 0) / 4294967295;
}

function noise(x, y, z) {
  const i = Math.floor(x);
  const j = Math.floor(y);
  const k = Math.floor(z);
  const a = ease(x - i);
  const b = ease(y - j);
  const c = ease(z - k);
  const low = mix(mix(hash(i, j, k), hash(i + 1, j, k), a), mix(hash(i, j + 1, k), hash(i + 1, j + 1, k), a), b);
  const high = mix(mix(hash(i, j, k + 1), hash(i + 1, j, k + 1), a), mix(hash(i, j + 1, k + 1), hash(i + 1, j + 1, k + 1), a), b);
  return mix(low, high, c) * 2 - 1;
}

function smoothMin(a, b, width) {
  const overlap = Math.max(width - Math.abs(a - b), 0) / width;
  return Math.min(a, b) - overlap * overlap * width * 0.25;
}

const cubeFaces = [
  (u, v, n) => [n, v, -u],
  (u, v, n) => [-n, v, u],
  (u, v, n) => [u, n, -v],
  (u, v, n) => [u, -n, v],
  (u, v, n) => [u, v, n],
  (u, v, n) => [-u, v, -n],
];

const fracturePlanes = [
  [0.85, 0.42, -0.32], [-0.81, 0.46, 0.36], [0.39, 0.79, 0.47],
  [-0.42, 0.81, -0.40], [0.21, 0.25, 0.94], [0.29, 0.34, -0.89],
  [0.76, -0.44, 0.48], [-0.44, -0.27, 0.85],
];

function point(mesh, x, y, z, material, variation) {
  const index = mesh.vertices.length / STRIDE;
  mesh.vertices.push(x, y, z, 0, 0, 0, material, variation);
  return index;
}

function addStageBlock(mesh) {
  const center = [-5.0, 0.18, 0.82];
  for (const face of cubeFaces) {
    const corners = [[-1, -1], [1, -1], [1, 1], [-1, 1]];
    const indices = corners.map(([u, v]) => {
      const position = face(u, v, 1).map((coordinate, axis) => center[axis] + coordinate * 0.30);
      return point(mesh, ...position, BLOCK, 0.5);
    });
    mesh.indices.push(indices[0], indices[1], indices[2], indices[0], indices[2], indices[3]);
  }
}

function addRock(mesh, center, radius, { turn = 0, hue = 0.35, detail = 14, erosion = 1, shelf = 0 } = {}) {
  const [cx, cy, cz] = center;
  const [rx, ry, rz] = radius;
  const seed = ++mesh.rockCount;
  const offset = seed * 3.731;
  const spin = Math.cos(turn);
  const sin = Math.sin(turn);
  const leanX = (hash(seed, 2, 1) - 0.5) * 0.36;
  const leanZ = (hash(seed, 7, 3) - 0.5) * 0.32;
  const power = 2.7 + hash(seed, 4, 1) * 1.35;
  const cuts = fracturePlanes.map(([x, y, z], i) => [x, y, z, 0.69 + hash(seed, i, 42) * 0.46]);
  const shared = new Map();
  const footExtension = cy + ry > 0.04 ? Math.max(0, cy - ry - lagoonBottom(cx, cz) + 0.48) : 0;

  for (const face of cubeFaces) {
    const grid = [];
    for (let j = 0; j <= detail; j++) {
      for (let i = 0; i <= detail; i++) {
        const [qx, qy, qz] = face(i * 2 - detail, j * 2 - detail, detail);
        const key = ((qx + detail) * (detail * 2 + 1) + qy + detail) * (detail * 2 + 1) + qz + detail;
        if (shared.has(key)) {
          grid.push(shared.get(key));
          continue;
        }

        const length = Math.hypot(qx, qy, qz);
        const x = qx / length;
        const y = qy / length;
        const z = qz / length;
        const curve = Math.abs(x) ** power + Math.abs(y) ** power + Math.abs(z) ** power;
        let envelope = curve ** (-1 / power);
        for (const [nx, ny, nz, h] of cuts) {
          const angle = nx * x + ny * y + nz * z;
          if (angle > 0.2) envelope = smoothMin(envelope, h / angle, 0.11);
        }

        const u = x * envelope;
        const v = y * envelope;
        const w = z * envelope;
        const shape = noise(2.35 * u + offset, 2.12 * v + 7.3, 2.52 * w);
        const joints = noise(4.6 * u + offset * 0.73 + shape, 4.05 * v, 3.8 * w + shape);
        const fracture = Math.exp(-8.5 * Math.abs(joints));
        const bedding = Math.sin((v + u * 0.28 - w * 0.19) * (21 + shelf * 9) + shape * 2.1 + offset);
        const seam = Math.max(bedding, 0) ** 9;
        const grit = noise(9.8 * u, 9.2 * v + offset, 11.1 * w);
        const flake = noise(17.1 * u, 16.5 * v + offset * 1.32, 16.2 * w);

        const outside = 1 + erosion * (shape * 0.18 - fracture * 0.115 - seam * (0.036 + shelf * 0.024) + grit * 0.055 + flake * 0.029);
        const localX = (u * outside + v * leanX) * rx;
        const localY = (v * outside + u * 0.075 - w * 0.055) * ry;
        const localZ = (w * outside + v * leanZ) * rz;
        const surfaceY = cy + localY;
        // Pull the submerged feet of exposed rocks into the bed, leaving the waterline intact.
        const yOffset = footExtension * ease(clamp(-surfaceY / Math.max(0.40, ry * 0.64), 0, 1));
        const weathering = noise((cx + localX) * 0.83, (cy + localY) * 0.91, (cz + localZ) * 0.86);
        const color = clamp(hue + shape * 0.16 + weathering * 0.18 + grit * 0.10 - fracture * 0.18 - seam * 0.09, 0.04, 0.97);
        const index = point(mesh, cx + spin * localX - sin * localZ, surfaceY - yOffset, cz + sin * localX + spin * localZ, ROCK, color);
        shared.set(key, index);
        grid.push(index);
      }
    }
    addGridIndices(mesh.indices, grid, detail);
  }

  // Approximate the footprint where a rock intersects the waterline.
  if (cy + ry > 0.13 && cy - ry < 0.13) {
    const cut = Math.sqrt(Math.max(0.13, 1 - (cy / ry) ** 2)) * 0.85;
    mesh.obstacles.push({
      x: cx,
      z: cz,
      rx: Math.hypot(rx * spin, rz * sin) * cut,
      rz: Math.hypot(rx * sin, rz * spin) * cut,
    });
  }
}

function addGridIndices(indices, grid, divisions) {
  const row = divisions + 1;
  for (let j = 0; j < divisions; j++) {
    for (let i = 0; i < divisions; i++) {
      const a = grid[j * row + i];
      const b = grid[j * row + i + 1];
      const c = grid[(j + 1) * row + i];
      const d = grid[(j + 1) * row + i + 1];
      if ((i + j) % 2 === 0) {
        indices.push(a, b, c, b, d, c);
      } else {
        indices.push(a, b, d, a, d, c);
      }
    }
  }
}

function lagoonBottom(x, z) {
  const distance = Math.hypot(x / 8.7, (z - 0.7) / 12.5);
  const shelves = ease(clamp((distance - 0.24) / 0.67, 0, 1));
  const channels = noise(0.27 * x + 5.4, 6.1, 0.22 * z - 8.7);
  const rockBed = noise(0.64 * x + 13.7, 2.8, 0.61 * z);
  const rubble = noise(1.53 * x, 8.9, 1.43 * z);
  const offshore = ease(clamp((z - 13) / 7, 0, 1));
  return Math.min(-0.22, mix(-3.31 + shelves * 2.58 + channels * 0.48 + rockBed * 0.30 + rubble * 0.14, -3.45 + channels * 0.55, offshore));
}

function addGround(mesh, size, divisions, heightAt, material) {
  const grid = [];
  for (let j = 0; j <= divisions; j++) {
    for (let i = 0; i <= divisions; i++) {
      const x = mix(-size, size, i / divisions);
      const z = mix(size, -size, j / divisions);
      const y = heightAt(x, z);
      let variation = 0.5;
      if (material === SEABED) {
        const deposits = noise(0.30 * x + 3.1, 6.8, 0.32 * z);
        const gravel = noise(0.88 * x, 9.1, 0.91 * z);
        variation = clamp(0.61 + deposits * 0.24 + gravel * 0.18 + (y + 1.6) * 0.055, 0.04, 0.96);
      }
      grid.push(point(mesh, x, y, z, material, variation));
    }
  }
  addGridIndices(mesh.indices, grid, divisions);
}

function addLagoon(mesh) {
  addGround(mesh, 26, 88, lagoonBottom, SEABED);
  const rock = (center, radius, options) => addRock(mesh, center, radius, options);

  // Closest stones receive direct sunlight and occupy the bottom and right edges.
  rock([0.2, 0.38, -7.5], [4.35, 2.06, 3.5], { turn: 0.20, hue: 0.80, detail: 26, erosion: 0.98, shelf: 0.42 });
  rock([-3.6, -0.04, -8.5], [2.42, 1.60, 2.25], { turn: -0.38, hue: 0.70, detail: 17 });
  rock([-6.9, 0.35, -5.3], [3.35, 2.86, 3.02], { turn: 0.23, hue: 0.79, detail: 24, shelf: 0.43 });
  rock([-8.4, 0.96, -1.7], [3.08, 3.55, 3.63], { turn: -0.36, hue: 0.65, detail: 24, erosion: 1.22, shelf: 0.73 });
  rock([-8.65, 1.70, 1.7], [3.10, 3.28, 3.1], { turn: 0.48, hue: 0.65, detail: 20, erosion: 1.25, shelf: 0.53 });
  rock([-7.45, 0.14, 1.02], [2.40, 1.74, 2.86], { turn: 1.10, hue: 0.76, detail: 18 });
  rock([-6.58, -0.06, -2.43], [1.38, 1.29, 2.07], { turn: 0.85, hue: 0.72, detail: 15 });
  rock([-5.9, -0.26, -7.0], [2.32, 1.26, 2.21], { turn: 0.77, hue: 0.83, detail: 16 });
  rock([-8.3, 0.34, 5.50], [3.35, 2.72, 3.19], { turn: -0.70, hue: 0.60, detail: 18, shelf: 0.64 });

  // Broken arcs of dark outcrops frame the water without hiding the outside horizon.
  rock([-7.65, 0.33, 8.70], [3.15, 2.84, 3.12], { turn: -0.87, hue: 0.46, detail: 18 });
  rock([-5.5, 0.34, 10.9], [2.95, 2.66, 2.98], { turn: 0.80, hue: 0.26, detail: 19, erosion: 1.14 });
  rock([-3.25, 1.99, 12.55], [2.59, 3.65, 2.96], { turn: 0.28, hue: 0.25, detail: 23, erosion: 1.14, shelf: 0.61 });
  rock([-1.0, 0.83, 11.78], [2.40, 2.75, 2.05], { turn: -0.78, hue: 0.28, detail: 18, erosion: 1.22 });
  rock([1.37, 0.72, 12.20], [1.95, 2.66, 2.6], { turn: 0.56, hue: 0.31, detail: 18, shelf: 0.47 });
  rock([4.77, 0.41, 11.02], [3.02, 2.80, 3.04], { turn: -0.83, hue: 0.29, detail: 18, erosion: 1.18 });
  rock([7.73, 0.42, 9.34], [3.15, 2.56, 3.62], { turn: 0.63, hue: 0.27, detail: 18, shelf: 0.67 });
  rock([9.48, 0.47, 7.29], [3.47, 2.85, 3.53], { turn: -0.42, hue: 0.35, detail: 17 });
  rock([10.05, 0.68, 2.75], [3.46, 3.05, 3.55], { turn: 0.53, hue: 0.30, detail: 20, erosion: 1.16 });
  rock([9.5, -0.58, -0.57], [2.3, 1.35, 2.47], { turn: -0.72, hue: 0.40, detail: 14 });
  rock([6.18, -0.17, -2.71], [2.43, 1.55, 1.78], { turn: 0.60, hue: 0.34, detail: 22, erosion: 1.21 });
  rock([7.04, -0.43, -3.62], [1.58, 1.17, 1.72], { turn: -0.21, hue: 0.51, detail: 14 });

  // A few isolated rocks and shelves break the surface and show the moving waterline.
  rock([-4.17, -0.05, 6.02], [2.36, 1.71, 2.12], { turn: 0.28, hue: 0.53, detail: 21, shelf: 0.45 });
  rock([-4.18, -0.54, 7.72], [1.45, 1.89, 1.48], { turn: -0.55, hue: 0.37, detail: 16 });
  rock([1.79, -0.23, 4.55], [1.04, 0.98, 0.88], { turn: 0.77, hue: 0.57, detail: 19, erosion: 1.28 });
  rock([1.10, -0.47, 4.93], [0.72, 0.83, 0.67], { turn: -0.55, hue: 0.49, detail: 12 });
  rock([-0.68, -0.54, 3.62], [0.37, 0.73, 0.34], { turn: -0.18, hue: 0.43, detail: 10 });
  rock([-1.85, -0.42, 2.47], [0.63, 0.54, 0.40], { turn: 0.32, hue: 0.56, detail: 11 });
  rock([-2.34, -0.64, -4.61], [0.61, 1.03, 0.73], { turn: -0.80, hue: 0.58, detail: 15, erosion: 1.17 });
  rock([2.18, -0.71, -3.88], [0.71, 0.85, 0.46], { turn: 0.25, hue: 0.46, detail: 13 });
  rock([3.19, -0.91, -2.58], [0.41, 0.98, 0.45], { turn: 0.91, hue: 0.38, detail: 10 });

  // The low rocks around the center are visible through clear water and in the caustics view.
  const sunkenOutcrops = [
    [[-1.10, -0.86], [1.32, 1.12, 1.26], 0.55],
    [[0.92, -1.45], [0.87, 0.53, 0.78], -0.83],
    [[-3.14, -2.37], [1.38, 0.85, 1.10], 0.68],
    [[2.75, 4.66], [1.32, 0.57, 1.02], 0.19],
    [[4.16, 2.63], [1.45, 0.91, 1.15], -0.61],
    [[-2.75, 4.35], [1.30, 0.74, 1.05], 0.39],
    [[2.65, -4.43], [1.11, 0.98, 1.51], 0.70],
    [[-4.72, -4.31], [1.48, 0.67, 1.42], 0.41],
    [[-0.29, 7.06], [1.03, 0.84, 1.16], -0.50],
  ];
  for (const [[x, z], radius, turn] of sunkenOutcrops) {
    const [, ry] = radius;
    const y = Math.min(-0.27 - ry * 1.14, lagoonBottom(x, z) + 0.34 * ry);
    rock([x, y, z], radius, { turn, hue: 0.31, detail: 10, erosion: 1.22 });
  }

  for (let i = 0; i < 25; i++) {
    const x = mix(-6.4, 6.7, hash(i, 9, 18));
    const z = mix(-5.8, 8.9, hash(i, 12, 8));
    const size = mix(0.17, 0.57, hash(i, 21, 32));
    const y = Math.min(-0.44 - size, lagoonBottom(x, z) + size * 0.32);
    rock([x, y, z], [size, size * 0.54, size * 0.82], { turn: hash(i, 11, 48) * Math.PI, hue: 0.39, detail: 5 });
  }
}

function normals(mesh) {
  const { vertices, indices } = mesh;
  for (let i = 0; i < indices.length; i += 3) {
    const a = indices[i] * STRIDE;
    const b = indices[i + 1] * STRIDE;
    const c = indices[i + 2] * STRIDE;
    const ux = vertices[b] - vertices[a];
    const uy = vertices[b + 1] - vertices[a + 1];
    const uz = vertices[b + 2] - vertices[a + 2];
    const vx = vertices[c] - vertices[a];
    const vy = vertices[c + 1] - vertices[a + 1];
    const vz = vertices[c + 2] - vertices[a + 2];
    const x = uy * vz - uz * vy;
    const y = uz * vx - ux * vz;
    const z = ux * vy - uy * vx;
    vertices[a + 3] += x;
    vertices[a + 4] += y;
    vertices[a + 5] += z;
    vertices[b + 3] += x;
    vertices[b + 4] += y;
    vertices[b + 5] += z;
    vertices[c + 3] += x;
    vertices[c + 4] += y;
    vertices[c + 5] += z;
  }

  for (let i = 0; i < vertices.length; i += STRIDE) {
    const m = Math.hypot(vertices[i + 3], vertices[i + 4], vertices[i + 5]) || 1;
    vertices[i + 3] /= m;
    vertices[i + 4] /= m;
    vertices[i + 5] /= m;
  }
}

export function createTerrain(scene = 'rockpool') {
  const mesh = { vertices: [], indices: [], obstacles: [], rockCount: 0 };
  if (scene === 'wave') {
    addGround(mesh, 64, 1, () => -0.12, STAGE);
    addStageBlock(mesh);
  } else {
    addLagoon(mesh);
  }
  normals(mesh);
  return {
    vertices: new Float32Array(mesh.vertices),
    indices: new Uint32Array(mesh.indices),
    obstacles: mesh.obstacles,
  };
}
