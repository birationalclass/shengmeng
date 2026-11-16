const RESOLUTION = 256;
const SIZE = 48;
const CELL_SIZE = SIZE / RESOLUTION;
const STEP = 1 / 60;
const WAVE_SPEED = 5.2;
// The Courant number is 0.46, below the 2-D stability limit of 1 / sqrt(2).
const LAPLACIAN_WEIGHT = (WAVE_SPEED * STEP / CELL_SIZE) ** 2;
const DAMPING = 0.009;
const MAX_STEPS = 5;

// The HPWater wave model uses a reflecting obstacle mask and an absorbing box edge.
// https://github.com/AshenOneArt/HPWater/tree/main/Core_Source_Preview/HanPiWater/FluidDynamics
function edgeRetention() {
  const spongeWidth = RESOLUTION * 0.1;
  const axisRetention = Float32Array.from({ length: RESOLUTION }, (_, i) => {
    const distance = Math.min(i, RESOLUTION - 1 - i);
    const t = Math.min(1, distance / spongeWidth);
    return t * t * (3 - 2 * t);
  });
  return Float32Array.from({ length: RESOLUTION ** 2 }, (_, i) => {
    const absorption = 1 - axisRetention[i % RESOLUTION] * axisRetention[Math.floor(i / RESOLUTION)];
    return 1 - absorption * absorption;
  });
}

export function createRipples(gl) {
  const texture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, texture);
  gl.texStorage2D(gl.TEXTURE_2D, 1, gl.R16F, RESOLUTION, RESOLUTION);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);

  const length = RESOLUTION ** 2;
  const absorption = edgeRetention();
  const obstacles = new Uint8Array(length);
  const left = new Int32Array(length);
  const right = new Int32Array(length);
  const down = new Int32Array(length);
  const up = new Int32Array(length);
  let previous = new Float32Array(length);
  let current = new Float32Array(length);
  let next = new Float32Array(length);
  let elapsed = 0;
  let waveLifetime = 0;
  const impulses = [];

  function upload() {
    gl.bindTexture(gl.TEXTURE_2D, texture);
    gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, RESOLUTION, RESOLUTION, gl.RED, gl.FLOAT, current);
  }

  function reset() {
    elapsed = 0;
    waveLifetime = 0;
    impulses.length = 0;
    previous.fill(0);
    current.fill(0);
    next.fill(0);
    upload();
  }

  function setObstacleMask(mask) {
    if (!(mask instanceof Uint8Array) || mask.length !== length) {
      throw new TypeError('Expected a Uint8Array with one cell per ripple texel');
    }
    obstacles.set(mask);
    for (let i = 0; i < length; i++) {
      const x = i % RESOLUTION;
      // Reflect off rocks by using the center height for a blocked neighbor.
      left[i] = x > 0 && !obstacles[i - 1] ? i - 1 : i;
      right[i] = x < RESOLUTION - 1 && !obstacles[i + 1] ? i + 1 : i;
      down[i] = i >= RESOLUTION && !obstacles[i - RESOLUTION] ? i - RESOLUTION : i;
      up[i] = i < length - RESOLUTION && !obstacles[i + RESOLUTION] ? i + RESOLUTION : i;
    }
    reset();
  }

  function disturb(x, z, strength = 1, radius = 0.65) {
    if (!Number.isFinite(x) || !Number.isFinite(z) ||
        !Number.isFinite(strength) || !Number.isFinite(radius)) return;
    if (Math.abs(x) >= SIZE * 0.5 || Math.abs(z) >= SIZE * 0.5 || !strength) return;
    // Match the WebGL texture's texel-center convention for world-space sampling.
    const gridX = x / CELL_SIZE + RESOLUTION * 0.5 - 0.5;
    const gridZ = z / CELL_SIZE + RESOLUTION * 0.5 - 0.5;
    if (obstacles[Math.round(gridZ) * RESOLUTION + Math.round(gridX)]) return;

    const drop = {
      x: gridX,
      z: gridZ,
      strength: Math.max(-2, Math.min(2, strength)),
      radius: Math.max(CELL_SIZE, Math.min(3.5, radius)) / CELL_SIZE,
    };
    const last = impulses[impulses.length - 1];
    if (last && Math.hypot(last.x - gridX, last.z - gridZ) < drop.radius * 0.55) {
      impulses[impulses.length - 1] = drop;
    } else if (impulses.length < 64) {
      impulses.push(drop);
    }
    waveLifetime = 24;
  }

  function inject({ x, z, strength, radius }) {
    const radiusSquared = radius * radius;
    const inverseVariance = 1 / (2 * (radius * 0.4) ** 2);
    const leftEdge = Math.max(0, Math.ceil(x - radius));
    const rightEdge = Math.min(RESOLUTION - 1, Math.floor(x + radius));
    const lowerEdge = Math.max(0, Math.ceil(z - radius));
    const upperEdge = Math.min(RESOLUTION - 1, Math.floor(z + radius));
    for (let row = lowerEdge; row <= upperEdge; row++) {
      const rowDistance = (row - z) ** 2;
      for (let column = leftEdge; column <= rightEdge; column++) {
        const cell = row * RESOLUTION + column;
        const distanceSquared = rowDistance + (column - x) ** 2;
        if (obstacles[cell] || distanceSquared >= radiusSquared) continue;
        const weight = absorption[cell] * Math.exp(-distanceSquared * inverseVariance);
        const room = Math.max(0, 1 - Math.abs(next[cell]) / 0.28);
        next[cell] += 0.052 * strength * weight * room;
      }
    }
  }

  function step(deltaSeconds) {
    if (!(deltaSeconds > 0) || waveLifetime <= 0) return;
    elapsed += Math.min(deltaSeconds, STEP * MAX_STEPS);
    if (elapsed < STEP) return;
    while (elapsed >= STEP) {
      for (let i = 0; i < length; i++) {
        if (obstacles[i]) {
          next[i] = 0;
          continue;
        }
        const height = current[i];
        const laplacian = current[left[i]] + current[right[i]] + current[down[i]] + current[up[i]] - 4 * height;
        const momentum = (height - previous[i]) * (1 - DAMPING) * absorption[i];
        next[i] = height + momentum + LAPLACIAN_WEIGHT * laplacian;
      }
      for (const drop of impulses) inject(drop);
      impulses.length = 0;
      const spare = previous;
      previous = current;
      current = next;
      next = spare;
      elapsed -= STEP;
      waveLifetime -= STEP;
    }
    if (waveLifetime > 0) upload();
    else reset();
  }

  setObstacleMask(obstacles);
  return { texture, size: SIZE, resolution: RESOLUTION, step, disturb, reset, setObstacleMask };
}
