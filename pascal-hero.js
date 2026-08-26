(function registerPascalHero() {
  "use strict";

  const TAU = Math.PI * 2;
  const RX = 1.5;
  const RY = 0.84;
  // More than twice the previous relay range, still eased across the same
  // 9-second motion leg. The companion base layout keeps every full-cycle
  // Pascal intersection inside the conic throughout the wider travel.
  const RELAY_STEP_ANGLE = 0.8;
  const RELAY_MOVE_SECONDS = 9;
  const RELAY_HANDOFF_SECONDS = 1;
  const RELAY_PHASE_STEPS = [0, 1, 2, 1, 0, -1, -2, -1];
  const RELAY_DIRECTIONS = [1, 1, -1, -1, -1, -1, 1, 1];
  const STATIC_TIME = 14;
  // The physical order around the conic is A, E, C, F, B, D. Connecting the
  // labelled hexagon A-B-C-D-E-F therefore produces the familiar Pascal
  // configuration: AB/DE meet on the left, BC/EF on the right, and CD/FA near
  // the centre. All three intersections stay inside the fixed ellipse.
  const BASE_ANGLES = [2.52, -1.78048, 0.177963, -2.762482, 1.39834, -0.858647];
  const POINT_LABELS = ["A", "B", "C", "D", "E", "F"];
  // SIDE_PAIRS order is G = AB∩DE, K = BC∩EF, H = CD∩FA.
  const INTERSECTION_LABELS = ["G", "K", "H"];
  const SIDE_PAIRS = [[0, 3], [1, 4], [2, 5]];
  const PAIR_COLOURS = [
    "rgba(224, 102, 92, 0.88)",
    "rgba(83, 207, 219, 0.86)",
    "rgba(231, 185, 92, 0.88)"
  ];
  const PAIR_HEAD_RGB = [[224, 102, 92], [83, 207, 219], [231, 185, 92]];
  const EPSILON = 1e-10;

  function cross(first, second) {
    return [
      first[1] * second[2] - first[2] * second[1],
      first[2] * second[0] - first[0] * second[2],
      first[0] * second[1] - first[1] * second[0]
    ];
  }

  function lineThrough(first, second) {
    return cross([first.x, first.y, 1], [second.x, second.y, 1]);
  }

  function affineIntersection(firstLine, secondLine) {
    const homogeneous = cross(firstLine, secondLine);
    if (!Number.isFinite(homogeneous[2]) || Math.abs(homogeneous[2]) < EPSILON) return null;
    const x = homogeneous[0] / homogeneous[2];
    const y = homogeneous[1] / homogeneous[2];
    return Number.isFinite(x) && Number.isFinite(y) ? { x, y } : null;
  }

  function pointOnEllipse(angle) {
    return { x: RX * Math.cos(angle), y: RY * Math.sin(angle) };
  }

  function smootherstep(value) {
    const progress = Math.min(1, Math.max(0, value));
    return progress ** 3 * (progress * (progress * 6 - 15) + 10);
  }

  function createPascalHeroSimulation(options) {
    const settings = options || {};
    const canvas = settings.canvas || document.querySelector("#pascalHero");
    if (!canvas) return null;
    if (canvas.pascalHeroSimulation) return canvas.pascalHeroSimulation;

    const context = canvas.getContext("2d", { alpha: true, desynchronized: true });
    if (!context) return null;

    const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");
    let width = 1;
    let height = 1;
    let pixelRatio = 1;
    let elapsed = 0;
    let previousTimestamp = 0;
    let animationFrame = 0;
    let inViewport = true;
    let destroyed = false;

    function geometryAt(time) {
      const segmentDuration = RELAY_MOVE_SECONDS + RELAY_HANDOFF_SECONDS;
      const step = Math.floor(Math.max(0, time) / segmentDuration);
      const activeIndex = step % POINT_LABELS.length;
      const round = Math.floor(step / POINT_LABELS.length);
      const cycleRound = round % RELAY_PHASE_STEPS.length;
      const direction = RELAY_DIRECTIONS[cycleRound];
      const phase = RELAY_PHASE_STEPS[cycleRound] * RELAY_STEP_ANGLE;
      const segmentTime = Math.max(0, time) - step * segmentDuration;
      const rawProgress = Math.min(1, segmentTime / RELAY_MOVE_SECONDS);
      const progress = smootherstep(rawProgress);

      // Exactly one vertex changes angle during each relay leg. The other five
      // retain their completed offsets. Every intermediate point remains on the
      // ellipse, so Pascal's theorem applies at every rendered frame. Reversing
      // after two completed rounds keeps the full configuration tightly framed.
      const points = BASE_ANGLES.map((baseAngle, index) => {
        let offset = phase;
        if (index < activeIndex) offset += direction * RELAY_STEP_ANGLE;
        else if (index === activeIndex) offset += direction * RELAY_STEP_ANGLE * progress;
        return pointOnEllipse(baseAngle + offset);
      });
      const sides = points.map((point, index) => lineThrough(point, points[(index + 1) % points.length]));
      const intersections = SIDE_PAIRS.map(([first, second]) => affineIntersection(sides[first], sides[second]));
      if (intersections.some((point) => !point)) return null;

      const pascalLine = lineThrough(intersections[0], intersections[1]);
      const lineNorm = Math.hypot(pascalLine[0], pascalLine[1]);
      if (!Number.isFinite(lineNorm) || lineNorm < EPSILON) return null;
      const collinearityError = Math.max(...intersections.map((point) => Math.abs(
        pascalLine[0] * point.x + pascalLine[1] * point.y + pascalLine[2]
      ) / lineNorm));
      const conicError = Math.max(...points.map((point) => Math.abs(
        point.x * point.x / (RX * RX) + point.y * point.y / (RY * RY) - 1
      )));

      return {
        phase,
        points,
        sides,
        intersections,
        pascalLine,
        collinearityError,
        conicError,
        relay: {
          activeIndex,
          direction,
          moving: segmentTime < RELAY_MOVE_SECONDS,
          progress,
          rawProgress,
          round,
          step
        }
      };
    }

    function visualViewport() {
      const side = Math.max(18, width * 0.024);
      if (width < 620) {
        return {
          left: side,
          right: width - side,
          top: Math.max(52, height * 0.12),
          bottom: height - Math.max(28, height * 0.07)
        };
      }
      if (width < 980) {
        return {
          left: width * 0.24,
          right: width - side,
          top: Math.max(56, height * 0.075),
          bottom: height - Math.max(28, height * 0.06)
        };
      }
      return {
        left: width * 0.36,
        right: width - side,
        top: Math.max(58, height * 0.07),
        bottom: height - Math.max(30, height * 0.055)
      };
    }

    function createProjector() {
      const viewport = visualViewport();
      const viewportWidth = Math.max(1, viewport.right - viewport.left);
      const viewportHeight = Math.max(1, viewport.bottom - viewport.top);
      const scale = Math.min(viewportWidth / (RX * 2 + 0.18), viewportHeight / (RY * 2 + 0.22));
      const originX = (viewport.left + viewport.right) / 2;
      const originY = (viewport.top + viewport.bottom) / 2;
      return {
        viewport,
        scale,
        point: (worldPoint) => ({
          x: originX + worldPoint.x * scale,
          y: originY - worldPoint.y * scale
        })
      };
    }

    function conicLineSegment(line) {
      const [a, b, c] = line;
      const magnitudeSquared = a * a + b * b;
      if (magnitudeSquared < EPSILON) return null;
      const origin = { x: -a * c / magnitudeSquared, y: -b * c / magnitudeSquared };
      const inverseMagnitude = 1 / Math.sqrt(magnitudeSquared);
      const direction = { x: b * inverseMagnitude, y: -a * inverseMagnitude };
      const quadraticA = direction.x * direction.x / (RX * RX) + direction.y * direction.y / (RY * RY);
      const quadraticB = 2 * (
        origin.x * direction.x / (RX * RX) + origin.y * direction.y / (RY * RY)
      );
      const quadraticC = origin.x * origin.x / (RX * RX) + origin.y * origin.y / (RY * RY) - 1;
      const discriminant = quadraticB * quadraticB - 4 * quadraticA * quadraticC;
      if (!Number.isFinite(discriminant) || discriminant <= EPSILON) return null;
      const root = Math.sqrt(discriminant);
      const firstTime = (-quadraticB - root) / (2 * quadraticA);
      const secondTime = (-quadraticB + root) / (2 * quadraticA);
      return [
        { x: origin.x + direction.x * firstTime, y: origin.y + direction.y * firstTime },
        { x: origin.x + direction.x * secondTime, y: origin.y + direction.y * secondTime }
      ];
    }

    function drawEllipse(projector) {
      const traceEllipse = () => {
        context.beginPath();
        for (let index = 0; index <= 240; index += 1) {
          const point = projector.point(pointOnEllipse(TAU * index / 240));
          if (index === 0) context.moveTo(point.x, point.y);
          else context.lineTo(point.x, point.y);
        }
        context.closePath();
      };

      context.save();
      context.lineCap = "round";
      context.strokeStyle = "rgba(83, 207, 219, 0.18)";
      context.shadowColor = "rgba(83, 207, 219, 0.58)";
      context.shadowBlur = 24;
      context.lineWidth = 7;
      traceEllipse();
      context.stroke();
      context.shadowBlur = 0;
      context.strokeStyle = "rgba(120, 231, 219, 0.74)";
      context.lineWidth = 1.45;
      traceEllipse();
      context.stroke();
      context.restore();
    }

    function drawStarChords(points, projector) {
      context.save();
      context.lineJoin = "round";
      context.lineCap = "round";
      points.forEach((worldPoint, index) => {
        const nextWorldPoint = points[(index + 1) % points.length];
        const point = projector.point(worldPoint);
        const nextPoint = projector.point(nextWorldPoint);
        context.strokeStyle = PAIR_COLOURS[index % 3];
        context.globalAlpha = 0.82;
        context.lineWidth = 1.4;
        context.shadowColor = PAIR_COLOURS[index % 3];
        context.shadowBlur = 5;
        context.beginPath();
        context.moveTo(point.x, point.y);
        context.lineTo(nextPoint.x, nextPoint.y);
        context.stroke();
      });
      context.restore();
    }

    function drawPascalSegment(line, projector) {
      const worldSegment = conicLineSegment(line);
      if (!worldSegment) return;
      const first = projector.point(worldSegment[0]);
      const second = projector.point(worldSegment[1]);
      const extension = 0.07;
      const dx = second.x - first.x;
      const dy = second.y - first.y;
      const start = { x: first.x - dx * extension, y: first.y - dy * extension };
      const end = { x: second.x + dx * extension, y: second.y + dy * extension };
      context.save();
      context.lineCap = "round";
      context.strokeStyle = "rgba(232, 249, 243, 0.2)";
      context.lineWidth = 10;
      context.beginPath();
      context.moveTo(start.x, start.y);
      context.lineTo(end.x, end.y);
      context.stroke();
      context.strokeStyle = "rgba(244, 255, 251, 0.96)";
      context.shadowColor = "rgba(130, 240, 207, 0.72)";
      context.shadowBlur = 18;
      context.lineWidth = 1.65;
      context.beginPath();
      context.moveTo(start.x, start.y);
      context.lineTo(end.x, end.y);
      context.stroke();
      context.restore();
    }

    function drawDiamond(point, radius, stroke, fill, glow) {
      context.save();
      context.translate(point.x, point.y);
      context.rotate(Math.PI / 4);
      context.fillStyle = fill;
      context.strokeStyle = stroke;
      context.lineWidth = 1.25;
      context.shadowColor = glow;
      context.shadowBlur = 13;
      context.fillRect(-radius, -radius, radius * 2, radius * 2);
      context.strokeRect(-radius, -radius, radius * 2, radius * 2);
      context.restore();
    }

    function drawConicPoint(worldPoint, label, projector, active) {
      const point = projector.point(worldPoint);
      if (active) {
        context.save();
        const glow = context.createRadialGradient(point.x, point.y, 0, point.x, point.y, 14);
        glow.addColorStop(0, "rgba(246, 207, 129, 0.28)");
        glow.addColorStop(0.45, "rgba(130, 240, 207, 0.13)");
        glow.addColorStop(1, "rgba(130, 240, 207, 0)");
        context.fillStyle = glow;
        context.beginPath();
        context.arc(point.x, point.y, 14, 0, TAU);
        context.fill();
        context.strokeStyle = "rgba(246, 207, 129, 0.6)";
        context.lineWidth = 0.8;
        context.beginPath();
        context.arc(point.x, point.y, 8, 0, TAU);
        context.stroke();
        context.restore();
      }
      drawDiamond(
        point,
        active ? 4.2 : 3.2,
        active ? "rgba(246, 207, 129, 0.98)" : "rgba(130, 240, 207, 0.96)",
        "rgba(231, 246, 240, 0.94)",
        active ? "rgba(246, 207, 129, 0.95)" : "rgba(130, 240, 207, 0.85)"
      );
      context.save();
      context.fillStyle = active ? "rgba(255, 236, 190, 0.98)" : "rgba(220, 239, 232, 0.9)";
      context.font = `italic ${active ? "700" : "600"} ${active ? 13 : 12}px Georgia, "Times New Roman", serif`;
      const normalX = worldPoint.x / RX;
      const normalY = worldPoint.y / RY;
      context.textAlign = normalX < -0.24 ? "right" : normalX > 0.24 ? "left" : "center";
      context.textBaseline = normalY > 0.3 ? "bottom" : normalY < -0.3 ? "top" : "middle";
      context.fillText(label, point.x + normalX * 13, point.y - normalY * 13);
      context.restore();
    }

    function drawIntersection(worldPoint, label, colour, rgb, projector) {
      const point = projector.point(worldPoint);

      // Match the exact Chaos renderer's particle heads: a broad coloured
      // Gaussian-like halo pass followed by a compact, solid white core pass.
      context.save();
      context.globalCompositeOperation = "lighter";
      const halo = context.createRadialGradient(point.x, point.y, 0, point.x, point.y, 16);
      halo.addColorStop(0, `rgba(${rgb[0]}, ${rgb[1]}, ${rgb[2]}, 0.56)`);
      halo.addColorStop(0.24, `rgba(${rgb[0]}, ${rgb[1]}, ${rgb[2]}, 0.32)`);
      halo.addColorStop(0.58, `rgba(${rgb[0]}, ${rgb[1]}, ${rgb[2]}, 0.1)`);
      halo.addColorStop(1, `rgba(${rgb[0]}, ${rgb[1]}, ${rgb[2]}, 0)`);
      context.fillStyle = halo;
      context.beginPath();
      context.arc(point.x, point.y, 16, 0, TAU);
      context.fill();
      context.restore();

      context.save();
      context.fillStyle = colour;
      context.beginPath();
      context.arc(point.x, point.y, 5.4, 0, TAU);
      context.fill();
      context.fillStyle = "rgba(249, 255, 252, 0.98)";
      context.beginPath();
      context.arc(point.x, point.y, 2.55, 0, TAU);
      context.fill();
      context.restore();

      context.save();
      context.fillStyle = "rgba(255, 236, 190, 0.98)";
      context.shadowColor = "rgba(231, 185, 92, 0.6)";
      context.shadowBlur = 7;
      context.font = "italic 700 13px Georgia, \"Times New Roman\", serif";
      const labelOffsets = {
        G: { x: -12, y: -11, align: "right" },
        H: { x: 0, y: -14, align: "center" },
        K: { x: 12, y: 11, align: "left" }
      };
      const offset = labelOffsets[label] || { x: 11, y: -11, align: "left" };
      context.textAlign = offset.align;
      context.textBaseline = "middle";
      context.fillText(label, point.x + offset.x, point.y + offset.y);
      context.restore();
    }

    function drawCaption(geometry, projector) {
      const right = projector.viewport.right;
      const top = projector.viewport.top;
      context.save();
      context.textAlign = "right";
      context.fillStyle = "rgba(246, 207, 129, 0.82)";
      context.font = "700 9px ui-monospace, SFMono-Regular, Consolas, monospace";
      const activeLabel = POINT_LABELS[geometry.relay.activeIndex];
      context.fillText(
        width < 620
          ? `PASCAL · ${activeLabel} MOVES · G,H,K ∈ ℓP`
          : `PASCAL · ${activeLabel} MOVES / FIVE FIXED · G, H, K ONE LINE`,
        right,
        top + 2
      );
      context.fillStyle = "rgba(198, 226, 216, 0.72)";
      context.font = "8px ui-monospace, SFMono-Regular, Consolas, monospace";
      context.fillText(width < 620 ? "G=AB∩DE · K=BC∩EF · H=CD∩FA" : "G = AB ∩ DE   ·   K = BC ∩ EF   ·   H = CD ∩ FA", right, top + 18);
      context.fillStyle = "rgba(130, 240, 207, 0.66)";
      context.fillText(`G, H, K ∈ ℓP   ·   RESIDUAL ${Math.max(geometry.collinearityError, Number.EPSILON).toExponential(1)}`, right, top + 34);
      context.restore();
    }

    function render(time) {
      context.clearRect(0, 0, width, height);
      const geometry = geometryAt(time);
      if (!geometry) {
        canvas.dataset.geometry = "degenerate";
        return;
      }

      const projector = createProjector();
      canvas.dataset.geometry = "pascal";
      canvas.dataset.points = "A,B,C,D,E,F";
      canvas.dataset.intersections = "G,K,H";
      canvas.dataset.phase = geometry.phase.toFixed(4);
      canvas.dataset.activePoint = POINT_LABELS[geometry.relay.activeIndex];
      canvas.dataset.step = String(geometry.relay.step);
      canvas.dataset.stepAngle = RELAY_STEP_ANGLE.toFixed(2);
      canvas.dataset.stepProgress = geometry.relay.progress.toFixed(4);
      canvas.dataset.moving = String(geometry.relay.moving);
      canvas.dataset.collinearityError = geometry.collinearityError.toExponential(3);
      canvas.dataset.conicError = geometry.conicError.toExponential(3);

      context.save();
      const clip = projector.viewport;
      context.beginPath();
      context.rect(clip.left - 12, clip.top - 46, clip.right - clip.left + 24, clip.bottom - clip.top + 58);
      context.clip();
      context.globalAlpha = width < 620 ? 0.86 : 0.96;

      drawEllipse(projector);
      drawStarChords(geometry.points, projector);
      drawPascalSegment(geometry.pascalLine, projector);

      geometry.points.forEach((point, index) => drawConicPoint(
        point,
        POINT_LABELS[index],
        projector,
        index === geometry.relay.activeIndex
      ));
      geometry.intersections.forEach((point, index) => drawIntersection(
        point,
        INTERSECTION_LABELS[index],
        PAIR_COLOURS[index],
        PAIR_HEAD_RGB[index],
        projector
      ));
      context.restore();
      drawCaption(geometry, projector);
    }

    function fitCanvas() {
      const bounds = canvas.getBoundingClientRect();
      width = Math.max(1, bounds.width);
      height = Math.max(1, bounds.height);
      pixelRatio = Math.min(window.devicePixelRatio || 1, 2.5);
      const nextWidth = Math.round(width * pixelRatio);
      const nextHeight = Math.round(height * pixelRatio);
      if (canvas.width !== nextWidth || canvas.height !== nextHeight) {
        canvas.width = nextWidth;
        canvas.height = nextHeight;
      }
      context.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);
      render(reducedMotion.matches ? STATIC_TIME : elapsed);
    }

    function shouldRun() {
      return !destroyed && inViewport && !document.hidden && !reducedMotion.matches;
    }

    function animate(timestamp) {
      if (!shouldRun()) return;
      if (!previousTimestamp) previousTimestamp = timestamp;
      elapsed += Math.min(0.05, Math.max(0, (timestamp - previousTimestamp) / 1000));
      previousTimestamp = timestamp;
      render(elapsed);
      animationFrame = window.requestAnimationFrame(animate);
    }

    function updatePlayback() {
      window.cancelAnimationFrame(animationFrame);
      animationFrame = 0;
      canvas.dataset.running = String(shouldRun());
      if (shouldRun()) {
        previousTimestamp = 0;
        animationFrame = window.requestAnimationFrame(animate);
      } else {
        render(reducedMotion.matches ? STATIC_TIME : elapsed);
      }
    }

    const resizeObserver = typeof ResizeObserver === "function" ? new ResizeObserver(fitCanvas) : null;
    if (resizeObserver) resizeObserver.observe(canvas);
    else window.addEventListener("resize", fitCanvas);

    const intersectionObserver = typeof IntersectionObserver === "function"
      ? new IntersectionObserver(([entry]) => {
          inViewport = entry.isIntersecting;
          updatePlayback();
        }, { threshold: 0.01 })
      : null;
    if (intersectionObserver) intersectionObserver.observe(canvas);

    document.addEventListener("visibilitychange", updatePlayback);
    if (typeof reducedMotion.addEventListener === "function") reducedMotion.addEventListener("change", updatePlayback);
    else reducedMotion.addListener(updatePlayback);

    const api = {
      render,
      getState: () => ({
        running: shouldRun(),
        reducedMotion: reducedMotion.matches,
        inViewport,
        elapsed,
        phase: canvas.dataset.phase || null,
        activePoint: canvas.dataset.activePoint || null,
        step: canvas.dataset.step || null,
        stepProgress: canvas.dataset.stepProgress || null,
        moving: canvas.dataset.moving === "true",
        collinearityError: canvas.dataset.collinearityError || null,
        conicError: canvas.dataset.conicError || null
      }),
      destroy: () => {
        if (destroyed) return;
        destroyed = true;
        window.cancelAnimationFrame(animationFrame);
        document.removeEventListener("visibilitychange", updatePlayback);
        if (typeof reducedMotion.removeEventListener === "function") reducedMotion.removeEventListener("change", updatePlayback);
        else reducedMotion.removeListener(updatePlayback);
        if (resizeObserver) resizeObserver.disconnect();
        else window.removeEventListener("resize", fitCanvas);
        if (intersectionObserver) intersectionObserver.disconnect();
        delete canvas.pascalHeroSimulation;
      }
    };

    canvas.pascalHeroSimulation = api;
    fitCanvas();
    updatePlayback();
    return api;
  }

  window.createPascalHeroSimulation = createPascalHeroSimulation;
}());
