/* Course opening: deterministic particle geometry, no rendering or interaction.
 * E8 coordinates: AMS, Eight-dimensional spheres and the exceptional E8
 * https://mathvoices.ams.org/featurecolumn/2022/09/01/eight-dimensional-spheres-and-the-exceptional-e_8/
 * Projection interpretation: https://aimath.org/e8/mcmullen.html
 * Julia inverse iteration: Cornell MAT 331, Spring 2020, Project 2
 * https://e.math.cornell.edu/people/bdozier/mat331-spr20/projects/project2/proj2.pdf
 */
(function (root) {
  'use strict';

  const N = 72000;
  const TAU = Math.PI * 2;
  const names = [
    ['六瓣玫瑰', 'SIXFOLD ROSETTE', 6],
    ['八角星', 'EIGHT-POINTED STAR', 8],
    ['十二重花窗', 'TWELVEFOLD ROSETTE', 12]
  ];
  const captions = Object.freeze([
    { title: 'SIXFOLD ROSETTE', zh: '六瓣玫瑰', en: 'A turn of sixty degrees leaves the pattern unchanged.' },
    { title: 'EIGHT-POINTED STAR', zh: '八角星', en: 'Eightfold rotation and reflection shape the star.' },
    { title: 'TWELVEFOLD ROSETTE', zh: '十二重花窗', en: 'Twelvefold symmetry around a single centre.' },
    { title: 'Lie Group', zh: '李群', en: '240 roots in eight dimensions, projected onto a plane.' },
    { title: 'JULIA FRACTAL', zh: '朱利亚分形', en: 'One rule, iterated. An endlessly intricate boundary.' },
    { title: 'THE LORD OF THE RING', zh: '万环之环', en: 'A unique unital homomorphism from ℤ to every unital ring.' },
    { title: 'Platonic Solids', zh: '正多面体', en: 'Five Platonic solids. Three rotation groups.' },
    { title: 'Fundamental Group', zh: '基本群', en: 'The Möbius band retracts onto its core circle S¹.' },
    { title: 'Gauss · 17-Gon', zh: '高斯 · 尺规作图', en: 'A regular seventeen-sided polygon, constructible with compass and straightedge.' },
    { title: 'Galois Group', zh: '伽罗瓦群', en: 'Évariste Galois, 1811–1832. Galois Group.' }
  ].map(Object.freeze));
  const cache = new Array(captions.length);
  const spatialCache = new Array(captions.length);
  const normalCache = new Array(captions.length);
  const diagnostics = {
    count: N,
    patterns: names.map(item => ({ title: item[0], symmetry: 'D' + item[2] })),
    e8: { roots: 240, projected2d: 240, edges: 6720, rings: 8, rootsPerRing: 30, edgeParticles: 60480, rootParticles: 11520 },
    julia: { parameter: [-0.8, 0.156], map: 'z^2 + c', candidates: 600000, centralSymmetry: true },
    ropes: { interpretation: 'Circular sand ropes following the mathematical planar centre lines; the small tube radius is an artistic rendering, not an E8 or Julia dimension.', figures: [] },
    torus: { majorRadius: .67, minorRadius: .20, outerRadius: .87, innerRadius: .47, genus: 1, coordinateStride: 3, tiltDegrees: [55, -8, -18] }
  };

  let seed = 1;
  function resetRandom(value) { seed = value >>> 0; }
  function random() {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed / 4294967296;
  }
  function normal() {
    return Math.sqrt(-2 * Math.log(Math.max(1e-12, random()))) * Math.cos(TAU * random());
  }
  function dot(a, b) {
    let result = 0;
    for (let i = 0; i < a.length; i++) result += a[i] * b[i];
    return result;
  }
  function sortedPositions(points) {
    if (points.length !== N) throw new Error('Incorrect opening particle count: ' + points.length);
    for (const point of points) {
      const angle = Math.atan2(point[1], point[0]);
      point[2] = angle < 0 ? angle + TAU : angle;
      point[3] = point[0] * point[0] + point[1] * point[1];
    }
    points.sort((a, b) => a[2] - b[2] || a[3] - b[3]);
    const output = new Float32Array(N * 2);
    for (let i = 0; i < N; i++) {
      output[2 * i] = points[i][0];
      output[2 * i + 1] = points[i][1];
    }
    return output;
  }

  // Each point lies on a ROUND tube around a mathematical centre line.
  // The strand modulation is a shallow three-start helix, not a vertical
  // extrusion: every cross-section has the same scale in its two directions.
  function ropeSample(x, y, tx, ty, radius, phase, twist) {
    const length = Math.hypot(tx, ty) || 1;
    tx /= length; ty /= length;
    const ca = Math.cos(phase), sa = Math.sin(phase);
    const nx = -ty * ca, ny = tx * ca, nz = sa;
    const r = radius * (1 + .075 * Math.cos(3 * phase - twist));
    return [x + r * nx, y + r * ny, r * nz, nx, ny, nz,
      x, y, tx, ty, r];
  }
  function storeRopes(index, points, extra) {
    if (points.length !== N) throw new Error('Incorrect rope particle count');
    points.sort((a, b) => {
      const aa = (Math.atan2(a[1], a[0]) + TAU) % TAU;
      const ab = (Math.atan2(b[1], b[0]) + TAU) % TAU;
      return aa - ab || a[0] * a[0] + a[1] * a[1] - b[0] * b[0] - b[1] * b[1];
    });
    const flat = new Float32Array(N * 2), spatial = new Float32Array(N * 3), normals = new Float32Array(N * 3);
    let maximumNormalResidual = 0, maximumTangentDot = 0, maximumRadialResidual = 0;
    let minZ = Infinity, maxZ = -Infinity, minRadius = Infinity, maxRadius = 0;
    let crossSectionSideSquared = 0, crossSectionHeightSquared = 0;
    for (let i = 0; i < N; i++) {
      const p = points[i];
      for (let k = 0; k < 3; k++) { spatial[3 * i + k] = p[k]; normals[3 * i + k] = p[k + 3]; }
      flat[2 * i] = p[0]; flat[2 * i + 1] = p[1];
      maximumNormalResidual = Math.max(maximumNormalResidual, Math.abs(Math.hypot(p[3], p[4], p[5]) - 1));
      if (p.length > 6) {
        const dx = p[0] - p[6], dy = p[1] - p[7];
        const side = -p[9] * dx + p[8] * dy;
        maximumTangentDot = Math.max(maximumTangentDot, Math.abs(p[3] * p[8] + p[4] * p[9]));
        maximumRadialResidual = Math.max(maximumRadialResidual, Math.abs(Math.hypot(dx, dy, p[2]) - p[10]));
        crossSectionSideSquared += side * side; crossSectionHeightSquared += p[2] * p[2];
        minRadius = Math.min(minRadius, p[10]); maxRadius = Math.max(maxRadius, p[10]);
      }
      minZ = Math.min(minZ, p[2]); maxZ = Math.max(maxZ, p[2]);
      if (!p.slice(0, 6).every(Number.isFinite)) throw new Error('Non-finite rope particle');
    }
    cache[index] = flat; spatialCache[index] = spatial; normalCache[index] = normals;
    diagnostics.ropes.figures[index] = Object.assign({ title: captions[index].title, particles: N,
      crossSection: 'circular, with shallow three-start helical strand ridges',
      surfaceSampling: 'particles on the complete tube circumference; radial normals perpendicular to the local centre-line tangent',
      minimumRadius: minRadius, maximumRadius: maxRadius, minimumZ: minZ, maximumZ: maxZ,
      maximumNormalResidual, maximumTangentDot, maximumRadialResidual,
      crossSectionAspectRatio: Math.sqrt(crossSectionHeightSquared / crossSectionSideSquared)
    }, extra);
    return flat;
  }
  function polygonCurve(n, step, t, radius, phase) {
    const edge = Math.floor(t * n), f = t * n - edge;
    const a = TAU * edge / n + phase, b = TAU * (edge + step) / n + phase;
    const dx = radius * (Math.cos(b) - Math.cos(a)), dy = radius * (Math.sin(b) - Math.sin(a));
    return [radius * Math.cos(a) + f * dx, radius * Math.sin(a) + f * dy, dx, dy];
  }
  function motifCurve(kind) {
    const u = random() * .98, t = random() * TAU;
    let x, y, dx, dy, r, dr, radius = .014;
    if (kind === 0) {
      if (u < .50) {
        const a = Math.floor(random() * 6) * TAU / 6;
        const lx = .385 + .388 * Math.cos(t), ly = .171 * Math.sin(t);
        const ldx = -.388 * Math.sin(t), ldy = .171 * Math.cos(t);
        x = lx * Math.cos(a) - ly * Math.sin(a); y = lx * Math.sin(a) + ly * Math.cos(a);
        dx = ldx * Math.cos(a) - ldy * Math.sin(a); dy = ldx * Math.sin(a) + ldy * Math.cos(a);
        radius = .016;
      } else if (u < .70) { r = .51 + .22 * Math.cos(6 * t); dr = -1.32 * Math.sin(6 * t); radius = .014; }
      else if (u < .81) { r = .23 + .055 * Math.cos(6 * t); dr = -.33 * Math.sin(6 * t); radius = .012; }
      else if (u < .94) { r = random() < .6 ? .86 : .902; dr = 0; radius = .0115; }
      else {
        const a = Math.floor(random() * 12) * TAU / 12;
        x = .83 * Math.cos(a) + .035 * Math.cos(t); y = .83 * Math.sin(a) + .035 * Math.sin(t);
        dx = -.035 * Math.sin(t); dy = .035 * Math.cos(t); radius = .008;
      }
    } else if (kind === 1) {
      if (u < .54) { [x, y, dx, dy] = polygonCurve(8, 3, t / TAU, .89, Math.PI / 8); radius = .0165; }
      else if (u < .74) { [x, y, dx, dy] = polygonCurve(8, 3, t / TAU, .51, 0); radius = .013; }
      else if (u < .85) { r = random() < .62 ? .942 : .973; dr = 0; radius = .010; }
      else if (u < .94) { [x, y, dx, dy] = polygonCurve(8, 1, t / TAU, .76, Math.PI / 8); radius = .012; }
      else { r = .16; dr = 0; radius = .012; }
    } else {
      if (u < .43) {
        const a = Math.floor(random() * 12) * TAU / 12;
        const lx = .49 + .326 * Math.cos(t), ly = .103 * Math.sin(t);
        const ldx = -.326 * Math.sin(t), ldy = .103 * Math.cos(t);
        x = lx * Math.cos(a) - ly * Math.sin(a); y = lx * Math.sin(a) + ly * Math.cos(a);
        dx = ldx * Math.cos(a) - ldy * Math.sin(a); dy = ldx * Math.sin(a) + ldy * Math.cos(a); radius = .0135;
      } else if (u < .68) {
        const a = Math.floor(random() * 12) * TAU / 12;
        x = .655 * Math.cos(a) + .23 * Math.cos(t); y = .655 * Math.sin(a) + .23 * Math.sin(t);
        dx = -.23 * Math.sin(t); dy = .23 * Math.cos(t); radius = .012;
      } else if (u < .79) { r = .306 + .079 * Math.cos(12 * t); dr = -.948 * Math.sin(12 * t); radius = .012; }
      else if (u < .94) { r = random() < .62 ? .926 : .956; dr = 0; radius = .009; }
      else { r = .122; dr = 0; radius = .011; }
    }
    if (r !== undefined) {
      x = r * Math.cos(t); y = r * Math.sin(t);
      dx = dr * Math.cos(t) - r * Math.sin(t); dy = dr * Math.sin(t) + r * Math.cos(t);
    }
    return { x, y, dx, dy, radius, twist: t * 18 };
  }
  function makePattern(kind) {
    resetRandom(0x6a09e667 + kind * 104729);
    const order = names[kind][2], baseCount = N / (2 * order), points = [];
    for (let i = 0; i < baseCount; i++) {
      const c = motifCurve(kind), p = ropeSample(c.x, c.y, c.dx, c.dy, c.radius, random() * TAU, c.twist);
      // Apply the full dihedral orbit to the tube AND its normals. Symmetry
      // remains exact at the particle level, including the circular section.
      for (let j = 0; j < order; j++) for (const sign of [-1, 1]) {
        const a = j * TAU / order, co = Math.cos(a), si = Math.sin(a);
        const rotate = (x, y) => [x * co - sign * y * si, x * si + sign * y * co];
        const xy = rotate(p[0], p[1]), n = rotate(p[3], p[4]), centre = rotate(p[6], p[7]), tangent = rotate(p[8], p[9]);
        points.push([xy[0], xy[1], p[2], n[0], n[1], p[5], centre[0], centre[1], tangent[0], tangent[1], p[10]]);
      }
    }
    return storeRopes(kind, points, { symmetry: 'D' + order, centreLines: 'analytic petals, polar rosettes, polygon edges and circles' });
  }

  function makeE8() {
    resetRandom(0xe8124030);
    const roots = [];
    for (let i = 0; i < 8; i++) for (let j = i + 1; j < 8; j++) {
      for (const a of [-1, 1]) for (const b of [-1, 1]) {
        const vector = Array(8).fill(0); vector[i] = a; vector[j] = b; roots.push(vector);
      }
    }
    for (let mask = 0; mask < 256; mask++) {
      let negatives = 0;
      for (let i = 0; i < 8; i++) if (mask & (1 << i)) negatives++;
      if (negatives % 2 === 0) roots.push(Array.from({ length: 8 }, (_, i) => mask & (1 << i) ? -.5 : .5));
    }

    // Coxeter plane derived from the AMS simple roots by the first Fourier mode
    // of a Coxeter element of order 30. This is a genuine orthogonal projection.
    const u = [0.6698235723479292, 0.46350565994512927, 0.23693032605580572, 0, -0.23693032605580577, -0.4635056599451293, 0.09689906869984785, 0];
    const v = [0, -0.11911770226439813, -0.19273649092558648, -0.21763887165692936, -0.19273649092558642, -0.11911770226439801, 0, 0.9219330548851048];
    const projected = roots.map(r => [dot(r, u), dot(r, v)]);
    const maximumRadius = Math.max(...projected.map(p => Math.hypot(p[0], p[1])));
    const scale = .95 / maximumRadius;
    const nodes = projected.map(p => [p[0] * scale, p[1] * scale]);
    const rings = {};
    projected.forEach(p => {
      const radius = Math.hypot(p[0], p[1]).toFixed(8);
      rings[radius] = (rings[radius] || 0) + 1;
    });

    const points = [], allEdges = [];
    const lengthClasses = {};
    for (let i = 0; i < roots.length; i++) for (let j = i + 1; j < roots.length; j++) {
      if (dot(roots[i], roots[j]) !== 1) continue;
      const length = Math.hypot(nodes[i][0] - nodes[j][0], nodes[i][1] - nodes[j][1]);
      allEdges.push({ i, j, length });
      const key = length.toFixed(8);
      lengthClasses[key] = (lengthClasses[key] || 0) + 1;
    }
    const edges = allEdges.length;
    // The 6,720 true edges fall into eight projected-length classes of 840.
    // The shortest class is a complete union of 28 Coxeter orbits. Highlighting
    // this invariant skeleton keeps every root and reveals an open crystalline
    // web instead of scattering a few grains along thousands of long chords.
    const shortestLength = Math.min(...allEdges.map(edge => edge.length));
    const selectedEdges = allEdges.filter(edge => Math.abs(edge.length - shortestLength) < 1e-8);
    const coveredRoots = new Set();
    for (const edge of selectedEdges) {
      const { i, j } = edge;
      coveredRoots.add(i); coveredRoots.add(j);
      // Uniform midpoint samples also respect endpoint reversal, so the whole
      // particle skeleton retains the projection's exact 30-fold symmetry.
      for (let k = 0; k < 72; k++) {
        const t = (k + .5) / 72;
        const x = nodes[i][0] * (1 - t) + nodes[j][0] * t, y = nodes[i][1] * (1 - t) + nodes[j][1] * t;
        points.push(ropeSample(x, y, nodes[j][0] - nodes[i][0], nodes[j][1] - nodes[i][1], .0055, k * 2.399963229728653, t * 12 * TAU));
      }
    }
    // Each projected root is a small round bead. The coordinates of all 240
    // mathematical centres remain exact; no extra connections are introduced.
    for (const p of nodes) {
      for (let k = 0; k < 48; k++) {
        const z = 1 - 2 * (k + .5) / 48, ring = Math.sqrt(1 - z * z), a = k * 2.399963229728653;
        const nx = ring * Math.cos(a), ny = ring * Math.sin(a), radius = .0085;
        points.push([p[0] + radius * nx, p[1] + radius * ny, radius * z, nx, ny, z]);
      }
    }
    let rotationalError = 0;
    const co = Math.cos(TAU / 30), si = Math.sin(TAU / 30);
    for (const p of projected) {
      const x = co * p[0] - si * p[1], y = si * p[0] + co * p[1];
      let distance = Infinity;
      for (const q of projected) distance = Math.min(distance, Math.hypot(x - q[0], y - q[1]));
      rotationalError = Math.max(rotationalError, distance);
    }
    const rotation = projected.map(p => {
      const x = co * p[0] - si * p[1], y = si * p[0] + co * p[1];
      let nearest = -1, minimum = Infinity;
      projected.forEach((q, i) => {
        const distance = Math.hypot(x - q[0], y - q[1]);
        if (distance < minimum) { minimum = distance; nearest = i; }
      });
      return nearest;
    });
    const edgeKey = (i, j) => Math.min(i, j) + ':' + Math.max(i, j);
    const selectedKeys = new Set(selectedEdges.map(edge => edgeKey(edge.i, edge.j)));
    const unmatchedRotatedEdges = selectedEdges.filter(edge => !selectedKeys.has(edgeKey(rotation[edge.i], rotation[edge.j]))).length;
    Object.assign(diagnostics.e8, {
      roots: roots.length, projected2d: nodes.length, edges,
      ringPopulations: Object.values(rings), rotationalError,
      maximumRootRadius: .95, exactRootCentres: 240,
      renderedEdges: selectedEdges.length, edgeSelection: 'shortest projected length class',
      projectedLengthClasses: Object.values(lengthClasses), completeCoxeterOrbits: selectedEdges.length / 30,
      rootsCoveredBySkeleton: coveredRoots.size, unmatchedRotatedEdges,
      particlesPerRenderedEdge: 72, edgeParticles: selectedEdges.length * 72,
      rootParticles: roots.length * 48
    });
    if (roots.length !== 240 || edges !== 6720 || Object.keys(rings).length !== 8 || Object.values(rings).some(n => n !== 30) || selectedEdges.length !== 840 || coveredRoots.size !== 240 || unmatchedRotatedEdges !== 0) {
      throw new Error('E8 geometry verification failed');
    }
    return storeRopes(3, points, { centreLines: '840 true E8 edges from the shortest Coxeter-plane length class', rootBeads: 240, edgeRadius: .0055, beadRadius: .0085 });
  }

  function complexSqrt(x, y) {
    const radius = Math.hypot(x, y);
    if (radius === 0) return [0, 0];
    // Choose the large component first to avoid cancellation near either axis.
    if (x >= 0) {
      const real = Math.sqrt((radius + x) / 2);
      return [real, y / (2 * real)];
    }
    const imaginary = (y < 0 ? -1 : 1) * Math.sqrt((radius - x) / 2);
    return [Math.abs(y / (2 * imaginary)), imaginary];
  }
  function makeJulia() {
    resetRandom(0x03141592);
    const cx = -.8, cy = .156;
    const discriminant = complexSqrt(1 - 4 * cx, -4 * cy);
    let x = (1 + discriminant[0]) / 2, y = discriminant[1] / 2;
    if (2 * Math.hypot(x, y) <= 1) { x = (1 - discriminant[0]) / 2; y = -discriminant[1] / 2; }
    const startingPoint = [x, y], multiplierMagnitude = 2 * Math.hypot(x, y);
    if (multiplierMagnitude <= 1) throw new Error('Julia starting point must be repelling');

    // Explore BOTH inverse branches. A random backward orbit disproportionately
    // samples harmonic measure on exposed tips and misses the fine inner arms.
    // Each full-plane grid cell admits two descendants for further exploration;
    // this bounded branch tree reaches hundreds of inverse generations without
    // spending the budget on already densely sampled outer arcs.
    const grid = 2000, perCellLimit = 2, nodeLimit = 520000;
    const visits = new Uint8Array(grid * grid);
    const queue = new Float64Array(nodeLimit * 2), depths = new Uint16Array(nodeLimit);
    const halfPlane = new Map();
    let head = 0, tail = 1, occupiedCells = 0, maximumDepth = 0, inverseResidual = 0;
    queue[0] = x; queue[1] = y;
    while (head < tail && tail < nodeLimit - 2) {
      const previousX = queue[2 * head], previousY = queue[2 * head + 1];
      const nextDepth = depths[head] + 1;
      const preimage = complexSqrt(previousX - cx, previousY - cy);
      inverseResidual = Math.max(inverseResidual, Math.hypot(
        preimage[0] * preimage[0] - preimage[1] * preimage[1] + cx - previousX,
        2 * preimage[0] * preimage[1] + cy - previousY
      ));
      head++;
      for (const sign of [-1, 1]) {
        const px = preimage[0] * sign, py = preimage[1] * sign;
        const cellX = Math.floor((px + 2) * grid / 4), cellY = Math.floor((py + 2) * grid / 4);
        if (cellX < 0 || cellY < 0 || cellX >= grid || cellY >= grid) continue;
        const key = cellX + grid * cellY;
        if (visits[key] >= perCellLimit) continue;
        if (visits[key] === 0) occupiedCells++;
        visits[key]++;
        queue[2 * tail] = px; queue[2 * tail + 1] = py;
        depths[tail] = nextDepth; tail++;
        maximumDepth = Math.max(maximumDepth, nextDepth);
        if (py > 0 || (py === 0 && px >= 0)) {
          if (!halfPlane.has(key)) halfPlane.set(key, { point: [px, py], cellX, cellY });
        }
      }
    }

    // Visit coarse spatial cells in rounds, choosing one fine-cell sample from
    // each before taking another. All selected coordinates remain genuine
    // inverse-branch samples: no added interior fill, jitter or rotated copies.
    const coarse = new Map(), coarseGrid = grid / 2;
    for (const item of halfPlane.values()) {
      const key = Math.floor(item.cellX / 2) + coarseGrid * Math.floor(item.cellY / 2);
      let cell = coarse.get(key);
      if (!cell) { cell = []; coarse.set(key, cell); }
      cell.push(item.point);
    }
    const cells = Array.from(coarse.values());
    for (let i = cells.length - 1; i > 0; i--) {
      const j = Math.floor(random() * (i + 1)); [cells[i], cells[j]] = [cells[j], cells[i]];
    }
    const representatives = [];
    for (let layer = 0; layer < 4 && representatives.length < N / 2; layer++) {
      for (const cell of cells) {
        if (cell[layer]) representatives.push(cell[layer]);
        if (representatives.length === N / 2) break;
      }
    }
    if (representatives.length < N / 2) throw new Error('Insufficient Julia detail samples');
    const maximumRadius = Math.max(...representatives.map(p => Math.hypot(p[0], p[1])));
    const scale = .95 / maximumRadius, points = [];
    let innerSamples = 0, minimumRadius = Infinity;
    for (const p of representatives) {
      const radius = Math.hypot(p[0], p[1]);
      if (radius < .8) innerSamples++;
      minimumRadius = Math.min(minimumRadius, radius);
      const px = p[0] * scale, py = p[1] * scale;
      points.push([px, py], [-px, -py]);
    }
    Object.assign(diagnostics.julia, {
      parameter: [cx, cy], map: 'z^2 + c',
      method: 'deterministic inverse-branch tree; per-cell exploration cap; multiscale spatial sampling',
      approximation: 'finite floating-point sampling of the Julia set',
      candidates: tail, exploredNodes: head, branchTreeExhausted: head === tail,
      grid, perCellLimit, maximumInverseDepth: maximumDepth,
      startingPoint, multiplierMagnitude, inverseResidual,
      occupiedCells, occupiedHalfPlaneCells: halfPlane.size, coarseHalfPlaneCells: cells.length,
      selectedPairs: representatives.length, exactNegationPairs: representatives.length,
      fractionInsideRadiusPointEight: innerSamples / representatives.length,
      minimumUnscaledRadius: minimumRadius, maximumUnscaledRadius: maximumRadius, scale
    });
    return sortedPositions(points);
  }

  function makeTorus() {
    const major = .67, minor = .20;
    const ax = 55 * Math.PI / 180, ay = -8 * Math.PI / 180, az = -18 * Math.PI / 180;
    const cx = Math.cos(ax), sx = Math.sin(ax), cy = Math.cos(ay), sy = Math.sin(ay), cz = Math.cos(az), sz = Math.sin(az);
    function rotate(x, y, z) {
      const x1 = x, y1 = cx * y - sx * z, z1 = sx * y + cx * z;
      const x2 = cy * x1 + sy * z1, y2 = y1, z2 = -sy * x1 + cy * z1;
      return [cz * x2 - sz * y2, sz * x2 + cz * y2, z2];
    }
    const ex = rotate(1, 0, 0), ey = rotate(0, 1, 0), ez = rotate(0, 0, 1);
    // Rows of R, where p = R q. Its transpose returns to the un-tilted torus.
    const rotation = [ex[0], ey[0], ez[0], ex[1], ey[1], ez[1], ex[2], ey[2], ez[2]];
    const points = [];
    let meanTubeCosine = 0;
    function radicalInverse(value) {
      let result = 0, place = .5;
      while (value > 0) { result += (value & 1) * place; value = Math.floor(value / 2); place *= .5; }
      return result;
    }
    for (let i = 0; i < N; i++) {
      // Hammersley samples over the area measure. The torus area element is
      // r(R + r cos(v)) du dv, so invert v + (r/R) sin(v) = 2 pi t.
      // This avoids the overcrowded inner wall of uniform angle sampling.
      const u = TAU * (i + .5) / N;
      const t = TAU * ((radicalInverse(i) + .3819660112501051) % 1);
      let v = t;
      for (let k = 0; k < 7; k++) v -= (v + minor / major * Math.sin(v) - t) / (1 + minor / major * Math.cos(v));
      const cu = Math.cos(u), su = Math.sin(u), cv = Math.cos(v), sv = Math.sin(v);
      const p = rotate((major + minor * cv) * cu, (major + minor * cv) * su, minor * sv);
      const normal = rotate(cv * cu, cv * su, sv);
      const angle = Math.atan2(p[1], p[0]);
      points.push([p[0], p[1], p[2], normal[0], normal[1], normal[2], angle < 0 ? angle + TAU : angle, p[0] * p[0] + p[1] * p[1]]);
      meanTubeCosine += cv;
    }
    points.sort((a, b) => a[6] - b[6] || a[7] - b[7]);
    const spatial = new Float32Array(N * 3), normals = new Float32Array(N * 3), flat = new Float32Array(N * 2);
    let maximumSurfaceResidual = 0, maximumRadius = 0, minimumProjectedRadius = Infinity, maximumNormalResidual = 0;
    for (let i = 0; i < N; i++) {
      const p = points[i];
      spatial[3 * i] = p[0]; spatial[3 * i + 1] = p[1]; spatial[3 * i + 2] = p[2];
      normals[3 * i] = p[3]; normals[3 * i + 1] = p[4]; normals[3 * i + 2] = p[5];
      flat[2 * i] = p[0]; flat[2 * i + 1] = p[1];
      const x = spatial[3 * i], y = spatial[3 * i + 1], z = spatial[3 * i + 2];
      const localX = rotation[0] * x + rotation[3] * y + rotation[6] * z;
      const localY = rotation[1] * x + rotation[4] * y + rotation[7] * z;
      const localZ = rotation[2] * x + rotation[5] * y + rotation[8] * z;
      maximumSurfaceResidual = Math.max(maximumSurfaceResidual, Math.abs((Math.hypot(localX, localY) - major) ** 2 + localZ * localZ - minor * minor));
      maximumRadius = Math.max(maximumRadius, Math.hypot(x, y, z));
      minimumProjectedRadius = Math.min(minimumProjectedRadius, Math.hypot(x, y));
      maximumNormalResidual = Math.max(maximumNormalResidual, Math.abs(Math.hypot(normals[3 * i], normals[3 * i + 1], normals[3 * i + 2]) - 1));
      if (!Number.isFinite(x + y + z)) throw new Error('Non-finite torus particle');
    }
    Object.assign(diagnostics.torus, {
      particles: points.length, rotationMatrix: rotation,
      sampling: 'deterministic Hammersley surface-area measure; inverse area CDF',
      surfaceEquation: '(sqrt(x*x + y*y) - R)^2 + z*z = r*r, before the fixed tilt',
      maximumSurfaceResidual, maximumRadius, minimumProjectedRadius,
      maximumNormalResidual, meanTubeCosine: meanTubeCosine / N, expectedMeanTubeCosine: minor / (2 * major),
      integerRingCaption: 'Z is initial in the category of unital rings; the torus is a visual metaphor, not its underlying space'
    });
    if (points.length !== N || maximumRadius > .95 || maximumSurfaceResidual > 1e-6 || minimumProjectedRadius < .15) throw new Error('Torus geometry verification failed');
    cache[5] = flat;
    spatialCache[5] = spatial;
    normalCache[5] = normals;
  }

  let galoisBases=[],galoisNodes=[],galoisCompact=false;
  function makeGalois(){
    galoisNodes=Array.from({length:root.CourseOpeningGalois.nodeCount},(_,i)=>root.CourseOpeningGalois.sampleNode(N,i));
    const result=galoisNodes[0];cache[9]=result.flat;spatialCache[9]=result.positions;normalCache[9]=result.normals;
    galoisBases=galoisNodes.map(node=>node.positions.slice());
    diagnostics.galois={...root.CourseOpeningGalois.evidence(),componentCounts:result.componentCounts};
  }
  let polyhedra,topology;
  function makeTopology(){
    const result=topology=root.CourseOpeningTopology.sample(N);
    cache[7]=result.flat;spatialCache[7]=result.positions;normalCache[7]=result.normals;
    diagnostics.topology=root.CourseOpeningTopology.evidence();
  }
  function makeGauss(){
    const result=root.CourseOpeningGauss.sample(N);
    cache[8]=result.flat;spatialCache[8]=result.positions;normalCache[8]=result.normals;
    diagnostics.gauss={...root.CourseOpeningGauss.evidence(),componentCounts:result.componentCounts};
  }
  function makePolyhedra() {
    const result=polyhedra=root.CourseOpeningPolyhedra.sample(N);
    cache[6]=result.flat;spatialCache[6]=result.positions;normalCache[6]=result.normals;
    diagnostics.polyhedra=root.CourseOpeningPolyhedra.evidence();
  }

  function validateIndex(index) {
    if (!Number.isInteger(index) || index < 0 || index >= captions.length) throw new RangeError('Unknown opening geometry');
  }
  function create(index) {
    validateIndex(index);
    if (!cache[index]) {
      if (index === 9) makeGalois();
      else if (index === 8) makeGauss();
      else if (index === 7) makeTopology();
      else if (index === 6) makePolyhedra();
      else if (index === 5) makeTorus();
      else cache[index] = index < 3 ? makePattern(index) : index === 3 ? makeE8() : makeJuliaRopes();
    }
    return cache[index];
  }
  function makeJuliaRopes() {
    const flat = makeJulia(), cellSize = .012, cells = new Map();
    // PCA is local to the sampled inverse branches. It estimates their tangent
    // but never joins different samples with artificial line segments.
    const key = (x, y) => Math.floor(x / cellSize) + ',' + Math.floor(y / cellSize);
    for (let i = 0; i < N; i++) {
      const k = key(flat[2 * i], flat[2 * i + 1]);
      if (!cells.has(k)) cells.set(k, []);
      cells.get(k).push(i);
    }
    const points = [];
    let minimumNeighbours = Infinity, maximumNeighbours = 0;
    for (let i = 0; i < N / 2; i++) {
      const x = flat[2 * i], y = flat[2 * i + 1];
      const gx = Math.floor(x / cellSize), gy = Math.floor(y / cellSize);
      let xx = 0, xy = 0, yy = 0, neighbours = 0;
      for (let oy = -1; oy <= 1; oy++) for (let ox = -1; ox <= 1; ox++) {
        const nearby = cells.get((gx + ox) + ',' + (gy + oy));
        if (!nearby) continue;
        for (const j of nearby) {
          const dx = flat[2 * j] - x, dy = flat[2 * j + 1] - y;
          const d2 = dx * dx + dy * dy;
          if (d2 > .000144 || d2 < 1e-14) continue;
          const weight = Math.exp(-d2 / .00004);
          xx += weight * dx * dx; xy += weight * dx * dy; yy += weight * dy * dy; neighbours++;
        }
      }
      const a = .5 * Math.atan2(2 * xy, xx - yy);
      // A slim tube preserves the tiny branch gaps at normal viewing scale.
      const phase = i * 2.399963229728653;
      const p = ropeSample(x, y, Math.cos(a), Math.sin(a), .0052, phase, 86 * (x + .7 * y));
      points.push(p, [-p[0], -p[1], p[2], -p[3], -p[4], p[5], -p[6], -p[7], -p[8], -p[9], p[10]]);
      minimumNeighbours = Math.min(minimumNeighbours, neighbours); maximumNeighbours = Math.max(maximumNeighbours, neighbours);
    }
    return storeRopes(4, points, { centreLines: 'genuine inverse-branch samples; weighted local PCA tangents; no connecting chords', tubeRadius: .0052, minimumNeighbours, maximumNeighbours });
  }
  function closeupFocus(index) {
    validateIndex(index);
    if(index>=6)return [0,0,0];
    // Deterministic real surface coordinates, so a 10x shot lands on sand.
    const preferred = [[.66, .135], [.54, .40], [.76, .075], [.52, .12], [.28, .16], [.52, -.35]][index];
    const points = create3D(index);
    let nearest = 0, distance = Infinity;
    for (let i = 0; i < N; i++) {
      if (index < 5 && points[3 * i + 2] < (index < 3 ? .006 : .0025)) continue;
      const d = (points[3 * i] - preferred[0]) ** 2 + (points[3 * i + 1] - preferred[1]) ** 2 + Math.max(0, -points[3 * i + 2]) ** 2;
      if (d < distance) { distance = d; nearest = 3 * i; }
    }
    return Array.from(points.slice(nearest, nearest + 3));
  }
  function create3D(index) {
    validateIndex(index);
    if (!spatialCache[index]) {
      if (index === 9) makeGalois();
      else if (index === 8) makeGauss();
      else if (index === 7) makeTopology();
      else if (index === 6) makePolyhedra();
      else if (index === 5) makeTorus();
      else if (index === 4) makeJuliaRopes();
      else create(index);
    }
    return spatialCache[index];
  }
  function createNormals(index) {
    validateIndex(index);
    if (!normalCache[index]) {
      if (index === 9) makeGalois();
      else if (index === 8) makeGauss();
      else if (index === 7) makeTopology();
      else if (index === 6) makePolyhedra();
      else if (index === 5) makeTorus();
      else if (index === 4) makeJuliaRopes();
      else create(index);
    }
    return normalCache[index];
  }
  root.CourseOpeningGeometry = Object.freeze({
    count: N,
    captions,
    create,
    create3D,
    createNormals,
    closeupFocus,
    galoisNode(index){create3D(9);return galoisNodes[index];},
    fitGalois(compact){
      create3D(9);if(galoisCompact===compact)return false;galoisCompact=compact;
      const scale=compact?.66:1,offset=compact?-.34:0;
      galoisNodes.forEach((node,j)=>{const base=galoisBases[j];for(let i=0;i<N;i++){
        node.positions[i*3]=base[i*3]*scale;node.positions[i*3+1]=base[i*3+1]*scale+offset;node.positions[i*3+2]=base[i*3+2]*scale;
        node.flat[i*2]=node.positions[i*3];node.flat[i*2+1]=node.positions[i*3+1];
      }});return true;
    },
    pickPolyhedron(ray){create3D(6);return polyhedra.pick(ray.origin,ray.direction);},
    rotatePolyhedron(index,axis,angle){create3D(6);polyhedra.rotateSolid(index,axis,angle);},
    resetPolyhedra(){if(polyhedra)polyhedra.reset();if(topology)topology.reset();},
    pickTopology(ray){create3D(7);return topology.pick(ray.origin,ray.direction);},
    rotateTopology(index,axis,angle){create3D(7);topology.rotateObject(index,axis,angle);},
    evidence() { return JSON.parse(JSON.stringify({...diagnostics,polyhedronRotations:polyhedra?polyhedra.orientations():[],topologyRotations:topology?topology.orientations():[]})); }
  });
})(typeof window !== 'undefined' ? window : globalThis);
