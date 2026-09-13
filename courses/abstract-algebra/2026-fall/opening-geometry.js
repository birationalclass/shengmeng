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
    { title: '六瓣玫瑰', zh: '旋转六十度，图案与自身重合。', en: 'A turn of sixty degrees leaves the pattern unchanged.' },
    { title: '八角星', zh: '八重旋转与镜面对称，共同勾勒星形。', en: 'Eightfold rotation and reflection shape the star.' },
    { title: '十二重花窗', zh: '十二重对称，环绕同一个中心。', en: 'Twelvefold symmetry around a single centre.' },
    { title: 'E₈ 根系', zh: '240 个根，从八维空间投向平面。', en: '240 roots in eight dimensions, projected onto a plane.' },
    { title: 'Julia 分形', zh: '一条规则反复迭代，边界生出无尽细节。', en: 'One rule, iterated. An endlessly intricate boundary.' },
    { title: 'THE LORD OF THE RING', zh: '万环之环 ℤ', en: 'A unique unital homomorphism from ℤ to every unital ring.' }
  ].map(Object.freeze));
  const cache = new Array(captions.length);
  const spatialCache = new Array(captions.length);
  const normalCache = new Array(captions.length);
  const diagnostics = {
    count: N,
    patterns: names.map(item => ({ title: item[0], symmetry: 'D' + item[2] })),
    e8: { roots: 240, projected2d: 240, edges: 6720, rings: 8, rootsPerRing: 30, edgeParticles: 60480, rootParticles: 11520 },
    julia: { parameter: [-0.8, 0.156], map: 'z^2 + c', candidates: 600000, centralSymmetry: true },
    relief: { interpretation: 'Artistic grain-ridge extrusion of the unchanged XY diagrams; the added depth is not an E8 projection or a third Julia coordinate.', figures: [] },
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

  function pointOnPolygon(n, step, t, r, phase) {
    const edge = Math.floor(t * n), f = t * n - edge;
    const a = TAU * edge / n + phase, b = TAU * (edge + step) / n + phase;
    return [r * ((1 - f) * Math.cos(a) + f * Math.cos(b)), r * ((1 - f) * Math.sin(a) + f * Math.sin(b))];
  }
  function point(kind) {
    const u = random(), t = random() * TAU;
    let x, y, r;
    if (kind === 0) {
      if (u < .50) {
        const k = Math.floor(random() * 6), a = k * TAU / 6;
        const lx = .385 + .388 * Math.cos(t), ly = .171 * Math.sin(t);
        x = lx * Math.cos(a) - ly * Math.sin(a); y = lx * Math.sin(a) + ly * Math.cos(a);
      } else if (u < .70) { r = .51 + .22 * Math.cos(6 * t); x = r * Math.cos(t); y = r * Math.sin(t); }
      else if (u < .81) { r = .23 + .055 * Math.cos(6 * t); x = r * Math.cos(t); y = r * Math.sin(t); }
      else if (u < .94) { r = random() < .6 ? .86 : .902; x = r * Math.cos(t); y = r * Math.sin(t); }
      else if (u < .98) {
        const k = Math.floor(random() * 12), a = k * TAU / 12;
        r = .035; x = .83 * Math.cos(a) + r * Math.cos(t); y = .83 * Math.sin(a) + r * Math.sin(t);
      } else { r = Math.sqrt(random()) * .98; x = r * Math.cos(t); y = r * Math.sin(t); }
    } else if (kind === 1) {
      if (u < .54) [x, y] = pointOnPolygon(8, 3, random(), .89, Math.PI / 8);
      else if (u < .74) [x, y] = pointOnPolygon(8, 3, random(), .51, 0);
      else if (u < .85) { r = random() < .62 ? .942 : .973; x = r * Math.cos(t); y = r * Math.sin(t); }
      else if (u < .94) [x, y] = pointOnPolygon(8, 1, random(), .76, Math.PI / 8);
      else if (u < .98) { r = .16; x = r * Math.cos(t); y = r * Math.sin(t); }
      else { r = Math.sqrt(random()) * .99; x = r * Math.cos(t); y = r * Math.sin(t); }
    } else {
      if (u < .43) {
        const k = Math.floor(random() * 12), a = k * TAU / 12;
        const lx = .49 + .326 * Math.cos(t), ly = .103 * Math.sin(t);
        x = lx * Math.cos(a) - ly * Math.sin(a); y = lx * Math.sin(a) + ly * Math.cos(a);
      } else if (u < .68) {
        const k = Math.floor(random() * 12), a = k * TAU / 12;
        x = .655 * Math.cos(a) + .23 * Math.cos(t); y = .655 * Math.sin(a) + .23 * Math.sin(t);
      } else if (u < .79) { r = .306 + .079 * Math.cos(12 * t); x = r * Math.cos(t); y = r * Math.sin(t); }
      else if (u < .94) { r = random() < .62 ? .926 : .956; x = r * Math.cos(t); y = r * Math.sin(t); }
      else if (u < .98) { r = .122; x = r * Math.cos(t); y = r * Math.sin(t); }
      else { r = Math.sqrt(random()) * .98; x = r * Math.cos(t); y = r * Math.sin(t); }
    }
    const spread = u > .98 ? .012 : (random() < .92 ? .0034 : .011);
    return [x + normal() * spread, y + normal() * spread];
  }
  function makePattern(kind) {
    resetRandom(0x6a09e667 + kind * 104729);
    const order = names[kind][2], baseCount = N / (2 * order), points = [];
    for (let i = 0; i < baseCount; i++) {
      const p = point(kind), r = Math.hypot(p[0], p[1]);
      const a = Math.acos(Math.max(-1, Math.min(1, Math.cos(order * Math.atan2(p[1], p[0]))))) / order;
      // Replicating each sampled fundamental sector preserves exact D_n symmetry,
      // including the fine grain scattered around the mathematical curves.
      for (let j = 0; j < order; j++) for (const sign of [-1, 1]) {
        const angle = j * TAU / order + sign * a;
        points.push([r * Math.cos(angle), r * Math.sin(angle)]);
      }
    }
    return sortedPositions(points);
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
        points.push([nodes[i][0] * (1 - t) + nodes[j][0] * t, nodes[i][1] * (1 - t) + nodes[j][1] * t]);
      }
    }
    // Use one common local grain cloud, rotated with each root. The original
    // root itself is always retained, and no grain extends beyond radius .95.
    const cloud = [[0, 0]];
    for (let k = 1; k < 48; k++) cloud.push([normal() * .00165, normal() * .00165]);
    for (const p of nodes) {
      const angle = Math.atan2(p[1], p[0]), c = Math.cos(angle), s = Math.sin(angle);
      for (const grain of cloud) {
        let x = p[0] + c * grain[0] - s * grain[1], y = p[1] + s * grain[0] + c * grain[1];
        const radius = Math.hypot(x, y);
        if (radius > .95) { x *= .95 / radius; y *= .95 / radius; }
        points.push([x, y]);
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
      rootParticles: roots.length * cloud.length
    });
    if (roots.length !== 240 || edges !== 6720 || Object.keys(rings).length !== 8 || Object.values(rings).some(n => n !== 30) || selectedEdges.length !== 840 || coveredRoots.size !== 240 || unmatchedRotatedEdges !== 0) {
      throw new Error('E8 geometry verification failed');
    }
    return sortedPositions(points);
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

  function validateIndex(index) {
    if (!Number.isInteger(index) || index < 0 || index >= captions.length) throw new RangeError('Unknown opening geometry');
  }
  function create(index) {
    validateIndex(index);
    if (!cache[index]) {
      if (index === 5) makeTorus();
      else cache[index] = index < 3 ? makePattern(index) : index === 3 ? makeE8() : makeJulia();
    }
    return cache[index];
  }
  // A diagram becomes a raised sand relief, rather than a sheet of shaded dots.
  // Its original XY samples are never displaced: the extra dimension is an
  // artistic extrusion of the existing grain ridges. Most grains form the
  // upper crest, while others expose continuous walls and the lower surface.
  function reliefHash(value) {
    value = Math.imul(value ^ (value >>> 16), 0x7feb352d);
    value = Math.imul(value ^ (value >>> 15), 0x846ca68b);
    return ((value ^ (value >>> 16)) >>> 0) / 4294967296;
  }
  function reliefHeight(index, x, y) {
    const radius = Math.hypot(x, y), angle = Math.atan2(y, x);
    const order = index < 3 ? names[index][2] : index === 3 ? 30 : 2;
    const t = Math.max(0, Math.min(1, (radius - .12) / .26));
    const fade = t * t * (3 - 2 * t);
    return .105 + .016 * (1 - Math.min(1, radius * radius))
      + .009 * fade * Math.cos(order * angle) + .006 * Math.cos(TAU * radius * 2);
  }
  function reliefDensity(flat) {
    // The smallest Hessian direction estimates the cross-section of a local
    // ridge. Its walls can then catch light from the side instead of sharing
    // the top surface's normal, including at the E8 web and Julia branches.
    const size = 256, extent = 1.08, scale = (size - 1) / (2 * extent);
    let density = new Float32Array(size * size);
    for (let i = 0; i < N; i++) {
      const gx = (flat[2 * i] + extent) * scale, gy = (flat[2 * i + 1] + extent) * scale;
      const x = Math.floor(gx), y = Math.floor(gy), fx = gx - x, fy = gy - y;
      if (x < 0 || x >= size - 1 || y < 0 || y >= size - 1) continue;
      const cell = x + y * size;
      density[cell] += (1 - fx) * (1 - fy); density[cell + 1] += fx * (1 - fy);
      density[cell + size] += (1 - fx) * fy; density[cell + size + 1] += fx * fy;
    }
    for (let pass = 0; pass < 2; pass++) {
      const horizontal = new Float32Array(size * size), blurred = new Float32Array(size * size);
      for (let y = 0; y < size; y++) for (let x = 0; x < size; x++) {
        for (let offset = -2; offset <= 2; offset++) {
          horizontal[x + y * size] += density[Math.max(0, Math.min(size - 1, x + offset)) + y * size] / 5;
        }
      }
      for (let y = 0; y < size; y++) for (let x = 0; x < size; x++) {
        for (let offset = -2; offset <= 2; offset++) {
          blurred[x + y * size] += horizontal[x + Math.max(0, Math.min(size - 1, y + offset)) * size] / 5;
        }
      }
      density = blurred;
    }
    return function ridgeNormal(x, y, sign) {
      const gx = Math.max(1, Math.min(size - 2, Math.round((x + extent) * scale)));
      const gy = Math.max(1, Math.min(size - 2, Math.round((y + extent) * scale)));
      const cell = gx + gy * size, centre = density[cell];
      const xx = density[cell - 1] + density[cell + 1] - 2 * centre;
      const yy = density[cell - size] + density[cell + size] - 2 * centre;
      const xy = (density[cell + size + 1] - density[cell + size - 1]
        - density[cell - size + 1] + density[cell - size - 1]) * .25;
      const eigenvalue = (xx + yy - Math.hypot(xx - yy, 2 * xy)) * .5;
      let nx = xy, ny = eigenvalue - xx;
      if (Math.hypot(nx, ny) < 1e-8) {
        if (Math.abs(xx) + Math.abs(yy) < 1e-7) { nx = x; ny = y; }
        else { nx = xx < yy ? 1 : 0; ny = xx < yy ? 0 : 1; }
      }
      const length = Math.hypot(nx, ny) || 1;
      return [sign * nx / length, sign * ny / length];
    };
  }
  function makeRelief(index) {
    const flat = create(index), output = new Float32Array(N * 3), normals = new Float32Array(N * 3);
    const ridgeNormal = reliefDensity(flat), bottom = -.09;
    let minimumZ = Infinity, maximumZ = -Infinity, topGrains = 0, wallGrains = 0, bottomGrains = 0;
    let maximumNormalResidual = 0;
    for (let i = 0; i < N; i++) {
      const x = flat[2 * i], y = flat[2 * i + 1], height = reliefHeight(index, x, y);
      const selector = reliefHash(i + 1 + index * 104729);
      const layer = reliefHash(i + 0x51ed270b + index * 13007);
      const grain = reliefHash(i + 0x68bc21eb + index * 19001);
      let z, nx, ny, nz;
      if (selector < .56) {
        // A dense top crest preserves the original drawing even at a steep
        // camera angle; its low relief still follows the figure's symmetry.
        z = height + (grain - .5) * .003;
        const epsilon = .001;
        nx = -(reliefHeight(index, x + epsilon, y) - reliefHeight(index, x - epsilon, y)) / (2 * epsilon);
        ny = -(reliefHeight(index, x, y + epsilon) - reliefHeight(index, x, y - epsilon)) / (2 * epsilon);
        nz = 1; topGrains++;
      } else if (selector < .92) {
        // The intervening grains occupy actual depth, forming narrow walls
        // along existing curves rather than filling the empty parts of a motif.
        z = bottom + (height - bottom) * layer;
        const side = ridgeNormal(x, y, grain < .5 ? -1 : 1);
        nx = side[0]; ny = side[1]; nz = .10 + .12 * layer; wallGrains++;
      } else {
        z = bottom + (grain - .5) * .002;
        nx = 0; ny = 0; nz = -1; bottomGrains++;
      }
      const length = Math.hypot(nx, ny, nz);
      output[3 * i] = x; output[3 * i + 1] = y; output[3 * i + 2] = z;
      normals[3 * i] = nx / length; normals[3 * i + 1] = ny / length; normals[3 * i + 2] = nz / length;
      minimumZ = Math.min(minimumZ, output[3 * i + 2]); maximumZ = Math.max(maximumZ, output[3 * i + 2]);
      maximumNormalResidual = Math.max(maximumNormalResidual,
        Math.abs(Math.hypot(normals[3 * i], normals[3 * i + 1], normals[3 * i + 2]) - 1));
      if (!Number.isFinite(x + y + z + nx + ny + nz)) throw new Error('Non-finite relief particle');
    }
    diagnostics.relief.figures[index] = {
      title: captions[index].title, particles: N, xyUnchanged: true,
      minimumZ, maximumZ, thickness: maximumZ - minimumZ,
      topGrains, wallGrains, bottomGrains, maximumNormalResidual,
      construction: '56% raised crest; 36% continuous ridge walls; 8% lower surface; density-Hessian wall normals'
    };
    spatialCache[index] = output; normalCache[index] = normals;
  }
  function create3D(index) {
    validateIndex(index);
    if (!spatialCache[index]) {
      if (index === 5) makeTorus();
      else makeRelief(index);
    }
    return spatialCache[index];
  }
  function createNormals(index) {
    validateIndex(index);
    if (!normalCache[index]) {
      if (index === 5) makeTorus();
      else makeRelief(index);
    }
    return normalCache[index];
  }
  root.CourseOpeningGeometry = Object.freeze({
    count: N,
    captions,
    create,
    create3D,
    createNormals,
    evidence() { return JSON.parse(JSON.stringify(diagnostics)); }
  });
})(typeof window !== 'undefined' ? window : globalThis);
