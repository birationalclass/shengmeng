(() => {
  "use strict";

  const TAU = Math.PI * 2;
  const RX = 1.5;
  const RY = 0.84;
  const POINT_LABELS = ["A", "B", "C", "D", "E", "F"];
  const INTERSECTION_LABELS = ["G", "K", "H"];
  // Physical order A, E, C, F, B, D reproduces the classical self-crossing
  // Pascal configuration while the logical hexagon remains A-B-C-D-E-F.
  const BASE_ANGLES = [2.62, -1.55, 0.42, -2.55, 1.55, -0.82];
  const PAIR_COLORS = ["#e0665c", "#52cad4", "#ddb35b"];
  const SIDE_PAIRS = [[0, 3], [1, 4], [2, 5]];
  const PARALLEL_EPSILON = 0.018;
  const DEGENERATE_EPSILON = 1e-8;

  const canvas = document.getElementById("pascalCanvas");
  const context = canvas.getContext("2d", { alpha: true, desynchronized: true });
  const stage = document.getElementById("stage");
  const theoremPanel = document.querySelector(".theorem-panel");
  const residualReadout = document.getElementById("residualReadout");
  const theoremStatus = document.getElementById("theoremStatus");
  const projectiveNote = document.getElementById("projectiveNote");
  const pauseButton = document.getElementById("pauseButton");
  const pauseLabel = document.getElementById("pauseLabel");
  const pauseIcon = pauseButton.querySelector(".pause-icon");
  const resetButton = document.getElementById("resetButton");
  const autoCameraButton = document.getElementById("autoCameraButton");
  const fullscreenButton = document.getElementById("fullscreenButton");
  const speedControl = document.getElementById("speedControl");
  const speedOutput = document.getElementById("speedOutput");
  const pointOptions = [...document.querySelectorAll(".point-option")];
  const keysButton = document.getElementById("keysButton");
  const keyGuide = document.getElementById("keyGuide");
  const gestureHint = document.getElementById("gestureHint");
  const announcer = document.getElementById("announcer");
  const reducedMotionQuery = window.matchMedia("(prefers-reduced-motion: reduce)");

  if (!context) {
    stage.classList.add("is-unavailable");
    announcer.textContent = "Canvas is unavailable in this browser.";
    return;
  }

  const pointers = new Map();
  const stars = createStars(150);
  const state = {
    width: 1,
    height: 1,
    dpr: 1,
    phase: 0,
    offsets: [0, 0, 0, 0, 0, 0],
    speed: 1,
    paused: reducedMotionQuery.matches,
    autoCamera: !reducedMotionQuery.matches,
    selectedPoint: 0,
    lastTimestamp: null,
    lastStatusUpdate: 0,
    dragMode: null,
    activePointer: null,
    pinchDistance: null,
    pinchZoom: 1,
    pinchMidpoint: null,
    manualPanX: 0,
    manualPanY: 0,
    manualZoom: 1,
    lastInteraction: -Infinity,
    cameraX: 0,
    cameraY: 0,
    cameraScale: 210,
    view: { originX: 0, originY: 0, centerX: 0, centerY: 0, scale: 210 },
    geometry: null,
    hoverPoint: -1
  };

  function createStars(count) {
    let seed = 0x51a7c41;
    const random = () => {
      seed = (1664525 * seed + 1013904223) >>> 0;
      return seed / 4294967296;
    };
    return Array.from({ length: count }, () => ({
      x: random(),
      y: random(),
      size: 0.25 + random() * 0.85,
      alpha: 0.06 + random() * 0.24,
      gold: random() > 0.92
    }));
  }

  function cross(a, b) {
    return [
      a[1] * b[2] - a[2] * b[1],
      a[2] * b[0] - a[0] * b[2],
      a[0] * b[1] - a[1] * b[0]
    ];
  }

  function dot(a, b) {
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  }

  function norm(vector) {
    return Math.hypot(vector[0], vector[1], vector[2]);
  }

  function normalizeHomogeneous(vector) {
    const length = norm(vector);
    if (!Number.isFinite(length) || length < DEGENERATE_EPSILON) return null;
    let normalized = vector.map((value) => value / length);
    const pivot = normalized.find((value) => Math.abs(value) > DEGENERATE_EPSILON);
    if (pivot < 0) normalized = normalized.map((value) => -value);
    return normalized;
  }

  function normalizeLine(line) {
    const scale = Math.hypot(line[0], line[1]);
    if (!Number.isFinite(scale) || scale < DEGENERATE_EPSILON) return null;
    let normalized = line.map((value) => value / scale);
    if (normalized[0] < -DEGENERATE_EPSILON || (Math.abs(normalized[0]) <= DEGENERATE_EPSILON && normalized[1] < 0)) {
      normalized = normalized.map((value) => -value);
    }
    return normalized;
  }

  function wrapAngle(angle) {
    return Math.atan2(Math.sin(angle), Math.cos(angle));
  }

  function conicPoint(angle) {
    return [RX * Math.cos(angle), RY * Math.sin(angle), 1];
  }

  function choosePascalLine(intersections) {
    let best = null;
    let bestScore = -Infinity;
    for (let first = 0; first < intersections.length; first += 1) {
      for (let second = first + 1; second < intersections.length; second += 1) {
        if (!intersections[first] || !intersections[second]) continue;
        const candidate = cross(intersections[first], intersections[second]);
        const score = norm(candidate);
        if (score > bestScore) {
          bestScore = score;
          best = normalizeHomogeneous(candidate);
        }
      }
    }
    return bestScore > DEGENERATE_EPSILON ? best : null;
  }

  function buildGeometry() {
    const angles = BASE_ANGLES.map((angle, index) => wrapAngle(angle + state.phase + state.offsets[index]));
    const points = angles.map(conicPoint);
    const sides = points.map((point, index) => normalizeLine(cross(point, points[(index + 1) % points.length])));
    const intersections = SIDE_PAIRS.map(([first, second]) => {
      if (!sides[first] || !sides[second]) return null;
      return normalizeHomogeneous(cross(sides[first], sides[second]));
    });
    const pascalLine = choosePascalLine(intersections);
    const degenerate = sides.some((line) => !line) || intersections.some((point) => !point) || !pascalLine;

    let residual = Infinity;
    if (!degenerate) {
      residual = Math.max(...intersections.map((point) => Math.abs(dot(pascalLine, point))));
    }

    const finite = intersections.map((point) => {
      if (!point || Math.abs(point[2]) < PARALLEL_EPSILON) return null;
      const x = point[0] / point[2];
      const y = point[1] / point[2];
      if (!Number.isFinite(x) || !Number.isFinite(y)) return null;
      return { x, y };
    });

    const lineAtInfinity = Boolean(pascalLine && Math.hypot(pascalLine[0], pascalLine[1]) < PARALLEL_EPSILON);
    return { angles, points, sides, intersections, finite, pascalLine, lineAtInfinity, degenerate, residual };
  }

  function computeBounds(geometry) {
    const samples = [
      { x: -RX, y: -RY },
      { x: RX, y: RY },
      ...geometry.finite.filter(Boolean).filter((point) => Math.abs(point.x) < 8 && Math.abs(point.y) < 8)
    ];
    let minX = Infinity;
    let maxX = -Infinity;
    let minY = Infinity;
    let maxY = -Infinity;
    samples.forEach((point) => {
      minX = Math.min(minX, point.x);
      maxX = Math.max(maxX, point.x);
      minY = Math.min(minY, point.y);
      maxY = Math.max(maxY, point.y);
    });
    const width = Math.max(3.15, maxX - minX);
    const height = Math.max(1.84, maxY - minY);
    return { centerX: (minX + maxX) / 2, centerY: (minY + maxY) / 2, width, height };
  }

  function updateCamera(geometry, delta, timestamp) {
    const bounds = computeBounds(geometry);
    const compact = state.width < 821;
    const availableWidth = state.width * (compact ? 0.8 : 0.49);
    const availableHeight = state.height * (compact ? 0.52 : 0.68);
    const targetScale = Math.max(44, Math.min(340, availableWidth / bounds.width, availableHeight / bounds.height));
    const smoothing = 1 - Math.exp(-delta * 2.6);

    if (state.autoCamera) {
      state.cameraX += (bounds.centerX - state.cameraX) * smoothing;
      state.cameraY += (bounds.centerY - state.cameraY) * smoothing;
      state.cameraScale += (targetScale - state.cameraScale) * smoothing;
    }

    if (state.autoCamera && timestamp - state.lastInteraction > 2600) {
      const decay = Math.exp(-delta * 0.72);
      state.manualPanX *= decay;
      state.manualPanY *= decay;
      state.manualZoom = 1 + (state.manualZoom - 1) * decay;
    }

    const cinematic = state.autoCamera && !reducedMotionQuery.matches ? timestamp * 0.00011 : 0;
    const driftX = state.autoCamera && !reducedMotionQuery.matches ? Math.cos(cinematic * 1.21) * state.width * 0.012 : 0;
    const driftY = state.autoCamera && !reducedMotionQuery.matches ? Math.sin(cinematic * 0.83) * state.height * 0.012 : 0;
    const breathing = state.autoCamera && !reducedMotionQuery.matches ? 1 + Math.sin(cinematic * 0.61) * 0.018 : 1;
    state.view = {
      originX: state.width * 0.5 + driftX + state.manualPanX,
      originY: state.height * (compact ? 0.57 : 0.51) + driftY + state.manualPanY,
      centerX: state.cameraX,
      centerY: state.cameraY,
      scale: state.cameraScale * state.manualZoom * breathing
    };
  }

  function worldToScreen(point) {
    return {
      x: state.view.originX + (point.x - state.view.centerX) * state.view.scale,
      y: state.view.originY - (point.y - state.view.centerY) * state.view.scale
    };
  }

  function screenToWorld(x, y) {
    return {
      x: state.view.centerX + (x - state.view.originX) / state.view.scale,
      y: state.view.centerY - (y - state.view.originY) / state.view.scale
    };
  }

  function affinePoint(homogeneous) {
    if (!homogeneous || Math.abs(homogeneous[2]) < PARALLEL_EPSILON) return null;
    return { x: homogeneous[0] / homogeneous[2], y: homogeneous[1] / homogeneous[2] };
  }

  function drawStars() {
    context.save();
    for (const star of stars) {
      context.fillStyle = star.gold ? `rgba(221,179,91,${star.alpha})` : `rgba(125,235,201,${star.alpha})`;
      context.beginPath();
      context.arc(star.x * state.width, star.y * state.height, star.size, 0, TAU);
      context.fill();
    }
    context.restore();
  }

  function drawConic() {
    context.save();
    context.lineWidth = 1;
    context.strokeStyle = "rgba(125,235,201,0.42)";
    context.shadowColor = "rgba(125,235,201,0.32)";
    context.shadowBlur = 14;
    context.beginPath();
    for (let index = 0; index <= 180; index += 1) {
      const angle = TAU * index / 180;
      const screen = worldToScreen({ x: RX * Math.cos(angle), y: RY * Math.sin(angle) });
      if (index === 0) context.moveTo(screen.x, screen.y);
      else context.lineTo(screen.x, screen.y);
    }
    context.closePath();
    context.stroke();
    context.shadowBlur = 0;

    context.setLineDash([2, 8]);
    context.strokeStyle = "rgba(125,235,201,0.11)";
    const horizontalA = worldToScreen({ x: -RX * 1.22, y: 0 });
    const horizontalB = worldToScreen({ x: RX * 1.22, y: 0 });
    const verticalA = worldToScreen({ x: 0, y: -RY * 1.35 });
    const verticalB = worldToScreen({ x: 0, y: RY * 1.35 });
    context.beginPath();
    context.moveTo(horizontalA.x, horizontalA.y);
    context.lineTo(horizontalB.x, horizontalB.y);
    context.moveTo(verticalA.x, verticalA.y);
    context.lineTo(verticalB.x, verticalB.y);
    context.stroke();
    context.restore();
  }

  function drawInfiniteLine(line, color, alpha, dash) {
    if (!line) return;
    const denominator = line[0] * line[0] + line[1] * line[1];
    if (denominator < DEGENERATE_EPSILON) return;
    const closest = { x: -line[0] * line[2] / denominator, y: -line[1] * line[2] / denominator };
    const direction = { x: -line[1], y: line[0] };
    const reach = 80;
    const first = worldToScreen({ x: closest.x - direction.x * reach, y: closest.y - direction.y * reach });
    const second = worldToScreen({ x: closest.x + direction.x * reach, y: closest.y + direction.y * reach });
    context.save();
    context.globalAlpha = alpha;
    context.strokeStyle = color;
    context.lineWidth = 0.8;
    context.setLineDash(dash || [4, 8]);
    context.beginPath();
    context.moveTo(first.x, first.y);
    context.lineTo(second.x, second.y);
    context.stroke();
    context.restore();
  }

  function drawSideConstruction(geometry) {
    SIDE_PAIRS.forEach(([first, second], pairIndex) => {
      drawInfiniteLine(geometry.sides[first], PAIR_COLORS[pairIndex], 0.19, [3, 10]);
      drawInfiniteLine(geometry.sides[second], PAIR_COLORS[pairIndex], 0.19, [3, 10]);
    });

    context.save();
    context.lineJoin = "round";
    context.lineCap = "round";
    geometry.points.forEach((point, index) => {
      const next = geometry.points[(index + 1) % geometry.points.length];
      const firstScreen = worldToScreen({ x: point[0], y: point[1] });
      const secondScreen = worldToScreen({ x: next[0], y: next[1] });
      const color = PAIR_COLORS[index % 3];
      context.strokeStyle = color;
      context.globalAlpha = 0.72;
      context.lineWidth = 1.15;
      context.beginPath();
      context.moveTo(firstScreen.x, firstScreen.y);
      context.lineTo(secondScreen.x, secondScreen.y);
      context.stroke();
    });
    context.restore();
  }

  function drawPascalLine(geometry) {
    if (!geometry.pascalLine || geometry.lineAtInfinity) {
      if (geometry.lineAtInfinity) drawInfinityBanner();
      return;
    }
    const line = normalizeLine(geometry.pascalLine);
    if (!line) return;
    const denominator = line[0] * line[0] + line[1] * line[1];
    const closest = { x: -line[0] * line[2] / denominator, y: -line[1] * line[2] / denominator };
    const direction = { x: -line[1], y: line[0] };
    const first = worldToScreen({ x: closest.x - direction.x * 80, y: closest.y - direction.y * 80 });
    const second = worldToScreen({ x: closest.x + direction.x * 80, y: closest.y + direction.y * 80 });

    context.save();
    context.lineCap = "round";
    context.strokeStyle = "rgba(125,235,201,0.16)";
    context.lineWidth = 9;
    context.shadowColor = "rgba(125,235,201,0.45)";
    context.shadowBlur = 24;
    context.beginPath();
    context.moveTo(first.x, first.y);
    context.lineTo(second.x, second.y);
    context.stroke();
    context.shadowBlur = 0;
    context.strokeStyle = "rgba(125,235,201,0.92)";
    context.lineWidth = 1.25;
    context.beginPath();
    context.moveTo(first.x, first.y);
    context.lineTo(second.x, second.y);
    context.stroke();
    context.fillStyle = "rgba(125,235,201,0.78)";
    context.font = "8px SFMono-Regular, Consolas, monospace";
    context.letterSpacing = "0.08em";
    const labelPoint = worldToScreen({ x: closest.x + direction.x * 1.05, y: closest.y + direction.y * 1.05 });
    if (labelPoint.x > 20 && labelPoint.x < state.width - 80 && labelPoint.y > 30 && labelPoint.y < state.height - 30) {
      context.fillText("ℓP · PASCAL LINE", labelPoint.x + 8, labelPoint.y - 8);
    }
    context.restore();
  }

  function drawInfinityBanner() {
    const y = Math.max(33, state.height * 0.31);
    context.save();
    context.setLineDash([5, 9]);
    context.strokeStyle = "rgba(221,179,91,0.8)";
    context.lineWidth = 1;
    context.beginPath();
    context.moveTo(state.width * 0.31, y);
    context.lineTo(state.width * 0.69, y);
    context.stroke();
    context.fillStyle = "rgba(221,179,91,0.82)";
    context.font = "8px SFMono-Regular, Consolas, monospace";
    context.textAlign = "center";
    context.fillText("ℓP · LINE AT INFINITY", state.width * 0.5, y - 9);
    context.restore();
  }

  function drawPointMarker(screen, label, color, selected, ideal) {
    const radius = selected ? 6.2 : 4.6;
    context.save();
    context.translate(screen.x, screen.y);
    context.rotate(Math.PI / 4);
    context.fillStyle = "rgba(4,17,15,0.92)";
    context.strokeStyle = color;
    context.lineWidth = selected ? 1.8 : 1.1;
    context.shadowColor = color;
    context.shadowBlur = selected ? 18 : 9;
    context.fillRect(-radius, -radius, radius * 2, radius * 2);
    context.strokeRect(-radius, -radius, radius * 2, radius * 2);
    context.restore();

    context.save();
    context.fillStyle = selected ? "#e7f2ed" : color;
    context.font = `${selected ? 12 : 10}px Georgia, "Times New Roman", serif`;
    context.textAlign = "left";
    context.textBaseline = "middle";
    context.fillText(label + (ideal ? "∞" : ""), screen.x + 11, screen.y - 10);
    context.restore();
  }

  function colorWithAlpha(color, alpha) {
    const value = Number.parseInt(color.slice(1), 16);
    const red = (value >> 16) & 255;
    const green = (value >> 8) & 255;
    const blue = value & 255;
    return `rgba(${red},${green},${blue},${alpha})`;
  }

  function drawIntersectionMarker(screen, label, color, ideal) {
    const haloRadius = ideal ? 13.5 : 14.5;
    const halo = context.createRadialGradient(
      screen.x,
      screen.y,
      0,
      screen.x,
      screen.y,
      haloRadius
    );
    halo.addColorStop(0, colorWithAlpha(color, 0.82));
    halo.addColorStop(0.18, colorWithAlpha(color, 0.54));
    halo.addColorStop(0.48, colorWithAlpha(color, 0.18));
    halo.addColorStop(1, colorWithAlpha(color, 0));

    context.save();
    context.globalCompositeOperation = "lighter";
    context.fillStyle = halo;
    context.beginPath();
    context.arc(screen.x, screen.y, haloRadius, 0, TAU);
    context.fill();

    context.fillStyle = colorWithAlpha(color, 0.58);
    context.shadowColor = color;
    context.shadowBlur = 12;
    context.beginPath();
    context.arc(screen.x, screen.y, 4.4, 0, TAU);
    context.fill();
    context.restore();

    context.save();
    context.fillStyle = "#f7fffd";
    context.shadowColor = "rgba(255,255,255,0.92)";
    context.shadowBlur = 7;
    context.beginPath();
    context.arc(screen.x, screen.y, 2.25, 0, TAU);
    context.fill();
    context.restore();

    context.save();
    context.fillStyle = color;
    context.shadowColor = colorWithAlpha(color, 0.38);
    context.shadowBlur = 5;
    context.font = `11px Georgia, "Times New Roman", serif`;
    context.textAlign = "left";
    context.textBaseline = "middle";
    context.fillText(label + (ideal ? "∞" : ""), screen.x + 12, screen.y - 9);
    context.restore();
  }

  function idealScreenPoint(homogeneous, index) {
    let dx = homogeneous[0];
    let dy = -homogeneous[1];
    const length = Math.hypot(dx, dy) || 1;
    dx /= length;
    dy /= length;
    if (dx < -0.01 || (Math.abs(dx) < 0.01 && dy > 0)) {
      dx *= -1;
      dy *= -1;
    }
    const radiusX = Math.max(80, state.width * 0.34);
    const radiusY = Math.max(70, state.height * 0.3);
    const stagger = (index - 1) * 11;
    return {
      x: Math.min(state.width - 62, Math.max(62, state.width / 2 + dx * radiusX + stagger)),
      y: Math.min(state.height - 105, Math.max(42, state.height / 2 + dy * radiusY + stagger))
    };
  }

  function offscreenFinitePoint(affine) {
    const unbounded = worldToScreen(affine);
    const center = { x: state.width / 2, y: state.height / 2 };
    const dx = unbounded.x - center.x;
    const dy = unbounded.y - center.y;
    const safeX = Math.max(60, state.width / 2 - 62);
    const safeY = Math.max(45, state.height / 2 - 105);
    const ratio = Math.min(safeX / Math.max(Math.abs(dx), 0.001), safeY / Math.max(Math.abs(dy), 0.001));
    return { x: center.x + dx * ratio, y: center.y + dy * ratio };
  }

  function drawIntersections(geometry) {
    geometry.intersections.forEach((point, index) => {
      if (!point) return;
      const affine = affinePoint(point);
      if (affine) {
        const screen = worldToScreen(affine);
        if (screen.x > -35 && screen.x < state.width + 35 && screen.y > -35 && screen.y < state.height + 35) {
          drawIntersectionMarker(screen, INTERSECTION_LABELS[index], PAIR_COLORS[index], false);
          return;
        }
        const edge = offscreenFinitePoint(affine);
        context.save();
        context.strokeStyle = PAIR_COLORS[index];
        context.globalAlpha = 0.6;
        context.setLineDash([2, 5]);
        context.beginPath();
        context.moveTo(state.width / 2, state.height / 2);
        context.lineTo(edge.x, edge.y);
        context.stroke();
        context.restore();
        drawIntersectionMarker(edge, INTERSECTION_LABELS[index], PAIR_COLORS[index], false);
        return;
      }
      const screen = idealScreenPoint(point, index);
      context.save();
      context.strokeStyle = PAIR_COLORS[index];
      context.globalAlpha = 0.72;
      context.setLineDash([2, 5]);
      context.beginPath();
      context.moveTo(state.width / 2, state.height / 2);
      context.lineTo(screen.x, screen.y);
      context.stroke();
      context.restore();
      drawIntersectionMarker(screen, INTERSECTION_LABELS[index], PAIR_COLORS[index], true);
    });
  }

  function drawConicPoints(geometry) {
    geometry.points.forEach((point, index) => {
      const screen = worldToScreen({ x: point[0], y: point[1] });
      drawPointMarker(screen, POINT_LABELS[index], index === state.selectedPoint ? "#7debc9" : "#e7f2ed", index === state.selectedPoint, false);
    });
  }

  function draw(timestamp) {
    context.clearRect(0, 0, state.width, state.height);
    drawStars();
    drawConic();
    if (state.geometry) drawSideConstruction(state.geometry);
    if (state.geometry && !state.geometry.degenerate) drawPascalLine(state.geometry);
    if (state.geometry) drawIntersections(state.geometry);
    if (state.geometry) drawConicPoints(state.geometry);

    context.save();
    context.fillStyle = "rgba(125,235,201,0.18)";
    context.font = "7px SFMono-Regular, Consolas, monospace";
    context.fillText(`CONIC q(x,y)=x²/${(RX * RX).toFixed(2)}+y²/${(RY * RY).toFixed(2)}−1`, 22, state.height - 92);
    context.fillText(`t ${(state.phase % TAU).toFixed(3)} · ${state.paused ? "PAUSED" : "LIVE"} · ${formatSpeed(state.speed)}`, 22, state.height - 77);
    context.restore();
  }

  function formatSpeed(value) {
    const rounded = Math.round(value * 100) / 100;
    return `${Number.isInteger(rounded) ? rounded.toFixed(0) : String(rounded).replace(/^0/, "")}×`;
  }

  function formatResidual(value) {
    if (!Number.isFinite(value)) return "—";
    return value.toExponential(2).replace("e-", "e−");
  }

  function updateStatus(geometry) {
    theoremPanel.classList.toggle("is-degenerate", geometry.degenerate);
    theoremPanel.classList.remove("is-projective");
    residualReadout.textContent = formatResidual(geometry.residual);

    if (geometry.degenerate) {
      theoremStatus.textContent = "DEGENERATE";
      projectiveNote.textContent = "Two vertices or defining lines coincide. Move the selected point to restore the construction.";
      return;
    }

    const idealLabels = geometry.finite
      .map((point, index) => point ? null : INTERSECTION_LABELS[index])
      .filter(Boolean);
    if (geometry.lineAtInfinity) {
      theoremPanel.classList.add("is-projective");
      theoremStatus.textContent = "LINE AT ∞";
      projectiveNote.textContent = "The three opposite-side pairs are parallel; their ideal points lie on the line at infinity.";
    } else if (idealLabels.length) {
      theoremPanel.classList.add("is-projective");
      theoremStatus.textContent = "PROJECTIVE";
      projectiveNote.textContent = `${idealLabels.join(", ")} ${idealLabels.length === 1 ? "is" : "are"} at infinity in this affine chart; Pascal collinearity persists in P².`;
    } else {
      theoremStatus.textContent = "COLLINEAR";
      projectiveNote.textContent = "All three intersections are finite in this affine chart.";
    }
  }

  function frame(timestamp) {
    const delta = state.lastTimestamp === null ? 0 : Math.min(0.05, Math.max(0, (timestamp - state.lastTimestamp) / 1000));
    state.lastTimestamp = timestamp;
    if (!state.paused && !document.hidden && state.dragMode !== "point") {
      state.phase = wrapAngle(state.phase + delta * state.speed * 0.105);
    }
    state.geometry = buildGeometry();
    updateCamera(state.geometry, delta, timestamp);
    draw(timestamp);
    if (timestamp - state.lastStatusUpdate > 160) {
      updateStatus(state.geometry);
      state.lastStatusUpdate = timestamp;
    }
    requestAnimationFrame(frame);
  }

  function resizeCanvas() {
    const rect = stage.getBoundingClientRect();
    state.width = Math.max(1, rect.width);
    state.height = Math.max(1, rect.height);
    state.dpr = Math.min(window.devicePixelRatio || 1, 2);
    canvas.width = Math.round(state.width * state.dpr);
    canvas.height = Math.round(state.height * state.dpr);
    canvas.style.width = `${state.width}px`;
    canvas.style.height = `${state.height}px`;
    context.setTransform(state.dpr, 0, 0, state.dpr, 0, 0);
    if (!state.geometry) state.geometry = buildGeometry();
    const bounds = computeBounds(state.geometry);
    const compact = state.width < 821;
    state.cameraX = bounds.centerX;
    state.cameraY = bounds.centerY;
    state.cameraScale = Math.max(44, Math.min(340,
      state.width * (compact ? 0.8 : 0.49) / bounds.width,
      state.height * (compact ? 0.52 : 0.68) / bounds.height
    ));
  }

  function updatePauseUI() {
    stage.classList.toggle("is-paused", state.paused);
    pauseButton.setAttribute("aria-pressed", String(state.paused));
    pauseLabel.textContent = state.paused ? "Continue" : "Pause";
    pauseIcon.textContent = state.paused ? "▶" : "Ⅱ";
    pauseButton.title = state.paused ? "Continue animation (P / Space)" : "Pause animation (P / Space)";
  }

  function togglePause(force) {
    state.paused = typeof force === "boolean" ? force : !state.paused;
    updatePauseUI();
    announcer.textContent = state.paused ? "Animation paused." : "Animation playing.";
  }

  function updateAutoCameraUI() {
    autoCameraButton.setAttribute("aria-pressed", String(state.autoCamera));
    autoCameraButton.textContent = state.autoCamera ? "Auto camera" : "Manual camera";
    autoCameraButton.title = state.autoCamera ? "Turn off cinematic camera (A / C)" : "Turn on cinematic camera (A / C)";
  }

  function setAutoCamera(value) {
    state.autoCamera = value;
    updateAutoCameraUI();
    announcer.textContent = value ? "Cinematic camera enabled." : "Cinematic camera disabled. Manual view preserved.";
  }

  function updateSelectedPoint(index, announce) {
    state.selectedPoint = (index + POINT_LABELS.length) % POINT_LABELS.length;
    pointOptions.forEach((button, buttonIndex) => {
      const selected = buttonIndex === state.selectedPoint;
      button.classList.toggle("is-active", selected);
      if (selected) button.setAttribute("aria-current", "true");
      else button.removeAttribute("aria-current");
      const small = button.querySelector("small");
      if (small) small.textContent = selected ? "SELECTED" : "ON CONIC";
    });
    if (announce !== false) announcer.textContent = `Point ${POINT_LABELS[state.selectedPoint]} selected.`;
  }

  function resetCamera() {
    state.manualPanX = 0;
    state.manualPanY = 0;
    state.manualZoom = 1;
    state.lastInteraction = -Infinity;
    state.geometry = buildGeometry();
    const bounds = computeBounds(state.geometry);
    state.cameraX = bounds.centerX;
    state.cameraY = bounds.centerY;
    const compact = state.width < 821;
    state.cameraScale = Math.max(44, Math.min(340,
      state.width * (compact ? 0.8 : 0.49) / bounds.width,
      state.height * (compact ? 0.52 : 0.68) / bounds.height
    ));
  }

  function resetAll() {
    state.phase = 0;
    state.offsets.fill(0);
    state.speed = 1;
    speedControl.value = "1";
    speedOutput.value = "1×";
    speedOutput.textContent = "1×";
    state.autoCamera = !reducedMotionQuery.matches;
    state.paused = reducedMotionQuery.matches;
    updateSelectedPoint(0, false);
    resetCamera();
    updatePauseUI();
    updateAutoCameraUI();
    announcer.textContent = "Pascal configuration, speed, and camera reset.";
  }

  function dismissGestureHint() {
    gestureHint.classList.add("is-dismissed");
  }

  function canvasCoordinates(event) {
    const rect = canvas.getBoundingClientRect();
    return { x: event.clientX - rect.left, y: event.clientY - rect.top };
  }

  function pointScreens() {
    const geometry = state.geometry || buildGeometry();
    return geometry.points.map((point) => worldToScreen({ x: point[0], y: point[1] }));
  }

  function nearestPoint(x, y, threshold) {
    let winner = -1;
    let bestDistance = threshold;
    pointScreens().forEach((point, index) => {
      const distance = Math.hypot(point.x - x, point.y - y);
      if (distance < bestDistance) {
        bestDistance = distance;
        winner = index;
      }
    });
    return winner;
  }

  function pointerDistance() {
    const active = [...pointers.values()];
    if (active.length < 2) return null;
    return Math.hypot(active[0].x - active[1].x, active[0].y - active[1].y);
  }

  function pointerMidpoint() {
    const active = [...pointers.values()];
    if (active.length < 2) return null;
    return { x: (active[0].x + active[1].x) / 2, y: (active[0].y + active[1].y) / 2 };
  }

  function markInteraction() {
    state.lastInteraction = performance.now();
    dismissGestureHint();
  }

  canvas.addEventListener("pointerdown", (event) => {
    if (event.pointerType === "mouse" && event.button !== 0) return;
    const point = canvasCoordinates(event);
    canvas.setPointerCapture(event.pointerId);
    pointers.set(event.pointerId, point);
    markInteraction();

    if (pointers.size >= 2) {
      state.dragMode = "pinch";
      state.pinchDistance = pointerDistance();
      state.pinchZoom = state.manualZoom;
      state.pinchMidpoint = pointerMidpoint();
      return;
    }

    const hit = nearestPoint(point.x, point.y, event.pointerType === "touch" ? 31 : 20);
    state.activePointer = event.pointerId;
    if (hit >= 0) {
      updateSelectedPoint(hit);
      state.dragMode = "point";
    } else {
      state.dragMode = "pan";
    }
  });

  canvas.addEventListener("pointermove", (event) => {
    const point = canvasCoordinates(event);
    const previous = pointers.get(event.pointerId);

    if (!previous) {
      const hit = nearestPoint(point.x, point.y, event.pointerType === "touch" ? 31 : 18);
      if (hit !== state.hoverPoint) {
        state.hoverPoint = hit;
        canvas.classList.toggle("is-point-hover", hit >= 0);
      }
      return;
    }

    pointers.set(event.pointerId, point);
    markInteraction();
    if (state.dragMode === "pinch" && pointers.size >= 2) {
      const distance = pointerDistance();
      const midpoint = pointerMidpoint();
      if (distance && state.pinchDistance) state.manualZoom = Math.min(2.8, Math.max(0.52, state.pinchZoom * distance / state.pinchDistance));
      if (midpoint && state.pinchMidpoint) {
        state.manualPanX += midpoint.x - state.pinchMidpoint.x;
        state.manualPanY += midpoint.y - state.pinchMidpoint.y;
        state.pinchMidpoint = midpoint;
      }
      return;
    }

    if (event.pointerId !== state.activePointer) return;
    if (state.dragMode === "point") {
      const world = screenToWorld(point.x, point.y);
      const angle = Math.atan2(world.y / RY, world.x / RX);
      state.offsets[state.selectedPoint] = wrapAngle(angle - BASE_ANGLES[state.selectedPoint] - state.phase);
      state.geometry = buildGeometry();
    } else if (state.dragMode === "pan") {
      state.manualPanX += point.x - previous.x;
      state.manualPanY += point.y - previous.y;
    }
  });

  function releasePointer(event) {
    const wasPointDrag = state.dragMode === "point";
    pointers.delete(event.pointerId);
    if (pointers.size >= 2) {
      state.pinchDistance = pointerDistance();
      state.pinchZoom = state.manualZoom;
      state.pinchMidpoint = pointerMidpoint();
      return;
    }
    if (pointers.size === 1) {
      const remaining = [...pointers.entries()][0];
      state.activePointer = remaining[0];
      state.dragMode = "pan";
      state.pinchDistance = null;
      state.pinchMidpoint = null;
      return;
    }
    state.dragMode = null;
    state.activePointer = null;
    state.pinchDistance = null;
    state.pinchMidpoint = null;
    if (wasPointDrag && state.geometry) {
      updateStatus(state.geometry);
      announcer.textContent = `Point ${POINT_LABELS[state.selectedPoint]} moved along the conic. ${theoremStatus.textContent.toLowerCase()}.`;
    }
  }

  canvas.addEventListener("pointerup", releasePointer);
  canvas.addEventListener("pointercancel", releasePointer);
  canvas.addEventListener("lostpointercapture", releasePointer);
  canvas.addEventListener("pointerleave", () => {
    if (!pointers.size) {
      state.hoverPoint = -1;
      canvas.classList.remove("is-point-hover");
    }
  });
  canvas.addEventListener("wheel", (event) => {
    event.preventDefault();
    const pixels = event.deltaY * (event.deltaMode === WheelEvent.DOM_DELTA_LINE
      ? 16
      : event.deltaMode === WheelEvent.DOM_DELTA_PAGE
        ? state.height
        : 1);
    state.manualZoom = Math.min(2.8, Math.max(0.52, state.manualZoom * Math.exp(-pixels * 0.0011)));
    markInteraction();
  }, { passive: false });
  canvas.addEventListener("dblclick", () => {
    resetCamera();
    announcer.textContent = "Camera framing reset.";
  });

  pauseButton.addEventListener("click", () => togglePause());
  resetButton.addEventListener("click", resetAll);
  autoCameraButton.addEventListener("click", () => setAutoCamera(!state.autoCamera));
  speedControl.addEventListener("input", () => {
    state.speed = Number(speedControl.value);
    const label = formatSpeed(state.speed);
    speedOutput.value = label;
    speedOutput.textContent = label;
  });
  pointOptions.forEach((button) => button.addEventListener("click", () => updateSelectedPoint(Number(button.dataset.point))));

  function fullscreenElement() {
    return document.fullscreenElement
      || document.webkitFullscreenElement
      || document.webkitCurrentFullScreenElement
      || null;
  }

  async function toggleFullscreen() {
    const ambientState = window.VisualLabAmbient && window.VisualLabAmbient.getState
      ? window.VisualLabAmbient.getState()
      : null;
    if (ambientState && ambientState.blocked && window.VisualLabAmbient.start) {
      window.VisualLabAmbient.start({ silent: true });
    }
    try {
      if (fullscreenElement()) {
        if (document.exitFullscreen) await document.exitFullscreen();
        else if (document.webkitExitFullscreen) document.webkitExitFullscreen();
        else if (document.webkitCancelFullScreen) document.webkitCancelFullScreen();
      }
      else if (stage.requestFullscreen) await stage.requestFullscreen();
      else if (stage.webkitRequestFullscreen) stage.webkitRequestFullscreen();
      else if (stage.webkitRequestFullScreen) stage.webkitRequestFullScreen();
      else announcer.textContent = "Full screen is unavailable in this browser.";
    } catch (_error) {
      announcer.textContent = "The browser did not allow full screen.";
    }
  }

  function updateFullscreenUI() {
    const active = fullscreenElement() === stage;
    const ambientControl = document.querySelector(".ambient-audio");
    if (ambientControl) (active ? stage : document.body).appendChild(ambientControl);
    fullscreenButton.setAttribute("aria-pressed", String(active));
    fullscreenButton.textContent = active ? "Exit full screen" : "Full screen";
    fullscreenButton.title = active ? "Leave full screen (F / F11)" : "Enter full screen (F / F11)";
    requestAnimationFrame(resizeCanvas);
  }

  fullscreenButton.addEventListener("click", toggleFullscreen);
  document.addEventListener("fullscreenchange", updateFullscreenUI);
  document.addEventListener("webkitfullscreenchange", updateFullscreenUI);

  keysButton.addEventListener("click", () => {
    if (typeof keyGuide.showModal === "function") keyGuide.showModal();
    else keyGuide.setAttribute("open", "");
    keysButton.setAttribute("aria-expanded", "true");
  });
  keyGuide.addEventListener("close", () => keysButton.setAttribute("aria-expanded", "false"));
  keyGuide.addEventListener("click", (event) => {
    if (event.target === keyGuide) keyGuide.close();
  });

  window.addEventListener("keydown", (event) => {
    const target = event.target;
    if (keyGuide.open || (target instanceof HTMLElement && target.closest("input, button, dialog, a"))) return;
    const key = event.key.toLowerCase();

    if (/^[1-6]$/.test(event.key)) {
      updateSelectedPoint(Number(event.key) - 1);
    } else if (event.key === "ArrowLeft" || event.key === "ArrowRight") {
      event.preventDefault();
      const direction = event.key === "ArrowRight" ? 1 : -1;
      state.offsets[state.selectedPoint] = wrapAngle(state.offsets[state.selectedPoint] + direction * (event.shiftKey ? 0.012 : 0.038));
      markInteraction();
      announcer.textContent = `Point ${POINT_LABELS[state.selectedPoint]} moved along the conic.`;
    } else if (event.code === "Space" || key === "p") {
      event.preventDefault();
      togglePause();
    } else if (key === "r") {
      resetAll();
    } else if (key === "a" || key === "c") {
      setAutoCamera(!state.autoCamera);
    } else if (key === "f" || event.key === "F11") {
      event.preventDefault();
      toggleFullscreen();
    } else if (event.key === "+" || event.key === "=") {
      state.manualZoom = Math.min(2.8, state.manualZoom * 1.12);
      markInteraction();
    } else if (event.key === "-" || event.key === "_") {
      state.manualZoom = Math.max(0.52, state.manualZoom / 1.12);
      markInteraction();
    }
  });

  reducedMotionQuery.addEventListener("change", (event) => {
    if (event.matches) {
      state.paused = true;
      state.autoCamera = false;
      updatePauseUI();
      updateAutoCameraUI();
      announcer.textContent = "Reduced motion enabled. Animation and cinematic camera paused.";
    }
  });

  document.addEventListener("visibilitychange", () => {
    state.lastTimestamp = null;
  });

  const resizeObserver = new ResizeObserver(resizeCanvas);
  resizeObserver.observe(stage);
  resizeCanvas();
  updatePauseUI();
  updateAutoCameraUI();
  updateFullscreenUI();
  updateSelectedPoint(0, false);

  window.PascalLab = Object.freeze({
    getSnapshot: () => ({
      speed: state.speed,
      paused: state.paused,
      autoCamera: state.autoCamera,
      selectedPoint: POINT_LABELS[state.selectedPoint],
      residual: state.geometry ? state.geometry.residual : null,
      idealIntersections: state.geometry ? state.geometry.finite.filter((point) => !point).length : null,
      lineAtInfinity: state.geometry ? state.geometry.lineAtInfinity : null
    })
  });

  requestAnimationFrame(frame);
})();
