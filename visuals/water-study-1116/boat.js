export function createBoat() {
  const vertices = [];
  const indices = [];
  const sections = [-1.38, -1.06, -0.60, 0, 0.58, 1.05, 1.43];
  const widths = [0.052, 0.37, 0.59, 0.64, 0.56, 0.35, 0.022];
  const rails = widths.map((width, i) => {
    const tip = Math.abs(sections[i]) / 1.43;
    return { width, z: sections[i], top: 0.38 + 0.24 * tip ** 4, base: -0.20 + 0.39 * tip ** 5 };
  });

  function triangle(a, b, c, variation, material = 3) {
    const u = b.map((value, i) => value - a[i]);
    const v = c.map((value, i) => value - a[i]);
    const n = [u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]];
    const length = Math.hypot(...n) || 1;
    const start = vertices.length / 8;
    for (const p of [a, b, c]) vertices.push(...p, ...n.map(q => q / length), material, variation);
    indices.push(start, start + 1, start + 2);
  }

  function quad(a, b, c, d, variation, material) {
    triangle(a, b, c, variation, material);
    triangle(a, c, d, variation, material);
  }

  function point(section, side, levels, index) {
    const width = section.width * levels[index][0];
    const height = section.base + (section.top - section.base) * levels[index][1];
    return [side * width, height, section.z];
  }

  const outer = [[0.02, 0], [0.48, 0.09], [0.81, 0.33], [0.97, 0.66], [1, 1]];
  const inner = [[0.025, 0.11], [0.42, 0.19], [0.70, 0.39], [0.86, 0.68], [0.90, 1]];
  for (const side of [-1, 1]) {
    for (let i = 0; i < rails.length - 1; i++) {
      const a = rails[i];
      const b = rails[i + 1];
      for (let row = 0; row < outer.length - 1; row++) {
        const shell = [point(a, side, outer, row), point(b, side, outer, row),
          point(b, side, outer, row + 1), point(a, side, outer, row + 1)];
        const lining = [point(a, side, inner, row), point(b, side, inner, row),
          point(b, side, inner, row + 1), point(a, side, inner, row + 1)];
        quad(...(side === 1 ? shell : shell.reverse()), 0.30 + row * 0.14, 3);
        quad(...(side === 1 ? lining.reverse() : lining), 0.17 + row * 0.05, 3);
      }
      const insideStart = point(a, side, inner, 4);
      const insideEnd = point(b, side, inner, 4);
      const outsideStart = point(a, side, outer, 4);
      const outsideEnd = point(b, side, outer, 4);
      quad(insideStart, insideEnd, outsideEnd, outsideStart, 0.86, 3);
    }
  }

  for (const [z, width, height] of [[-0.70, 0.41, 0.24], [-0.18, 0.53, 0.23], [0.52, 0.46, 0.27], [0.99, 0.25, 0.38]]) {
    quad([-width, height, z - 0.10], [-width, height, z + 0.10],
      [width, height, z + 0.10], [width, height, z - 0.10], 0.67, 3);
    quad([-width, height - 0.04, z - 0.10], [-width, height, z - 0.10],
      [width, height, z - 0.10], [width, height - 0.04, z - 0.10], 0.47, 3);
  }

  for (const z of [-0.65, -0.19, 0.31, 0.69]) {
    for (let i = 0; i < 5; i++) {
      const x = -0.30 + i * 0.12;
      quad([x, -0.12, z], [x, -0.12, z + 0.40], [x + 0.116, -0.12, z + 0.40], [x + 0.116, -0.12, z],
        0.36 + i * 0.09, 3);
    }
  }
  // The stern carries the low curved timber canopy visible in the reference.
  function canopy(x, z) {
    return 1.02 - 0.36 * x * x + (z + 0.78) * 0.035;
  }
  for (const x of [-0.38, 0.38]) {
    for (const z of [-1.05, -0.39]) {
      const y = canopy(x, z);
      quad([x - 0.022, 0.25, z], [x + 0.022, 0.25, z],
        [x + 0.022, y, z], [x - 0.022, y, z], 0.26, 3);
      quad([x, 0.25, z - 0.023], [x, 0.25, z + 0.023],
        [x, y, z + 0.023], [x, y, z - 0.023], 0.32, 3);
    }
  }
  for (let i = 0; i < 9; i++) {
    const a = -0.56 + 1.12 * i / 9;
    const b = a + 0.121;
    const z0 = -1.21 + 0.041 * Math.abs(a);
    const z1 = -0.27 - 0.071 * Math.abs(a);
    const corners = [[a, canopy(a,z0), z0], [a, canopy(a,z1), z1],
      [b, canopy(b,z1), z1], [b, canopy(b,z0), z0]];
    quad(...corners, 0.82 + 0.09 * Math.sin(i * 3.9), 4);
    const edge = [corners[0], corners[3], [b, canopy(b,z0) - 0.04, z0], [a, canopy(a,z0) - 0.04, z0]];
    quad(...edge, 0.56, 3);
  }
  return { vertices: new Float32Array(vertices), indices: new Uint32Array(indices) };
}
