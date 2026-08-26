(function registerPascalHero() {
  "use strict";

  const TAU = Math.PI * 2;
  const STATIC_TIME = 24;
  const BASE_ANGLES = [
    0.71168558,
    1.34876811,
    3.18530885,
    5.03071926,
    5.71081589,
    6.35150299
  ];
  const PHASES = [0, 1.1, 2.4, 3.2, 4.7, 5.5];
  const RATES = [0.17, 0.13, 0.11, 0.19, 0.15, 0.12];
  const AMPLITUDES = [0.065, 0.055, 0.06, 0.05, 0.06, 0.055];
  const POINT_LABELS = ["A", "B", "C", "D", "E", "F"];
  const ELLIPSE_ROTATION = -0.18;

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

  function intersection(firstLine, secondLine) {
    const homogeneous = cross(firstLine, secondLine);
    if (Math.abs(homogeneous[2]) < 1e-8) return null;
    return {
      x: homogeneous[0] / homogeneous[2],
      y: homogeneous[1] / homogeneous[2]
    };
  }

  function pointOnEllipse(angle) {
    const horizontal = Math.cos(angle);
    const vertical = 0.68 * Math.sin(angle);
    const cosine = Math.cos(ELLIPSE_ROTATION);
    const sine = Math.sin(ELLIPSE_ROTATION);
    return {
      x: horizontal * cosine - vertical * sine,
      y: horizontal * sine + vertical * cosine
    };
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

    function geometryAt(time) {
      const points = BASE_ANGLES.map((baseAngle, index) => pointOnEllipse(
        baseAngle + AMPLITUDES[index] * Math.sin(time * RATES[index] + PHASES[index])
      ));
      const sides = points.map((point, index) => lineThrough(point, points[(index + 1) % points.length]));
      const x = intersection(sides[0], sides[3]);
      const y = intersection(sides[1], sides[4]);
      const z = intersection(sides[2], sides[5]);
      if (!x || !y || !z) return null;
      const pascalLine = lineThrough(x, y);
      const divisor = Math.hypot(pascalLine[0], pascalLine[1]) || 1;
      const collinearityError = Math.abs(
        pascalLine[0] * z.x + pascalLine[1] * z.y + pascalLine[2]
      ) / divisor;
      return { points, sides, intersections: [x, y, z], pascalLine, collinearityError };
    }

    function createProjector() {
      const scale = Math.min(width * 0.54 / 3.25, height * 0.78 / 3.6);
      const centreX = width * 0.97 - 2.15 * scale;
      const centreY = height * 0.45;
      return {
        scale,
        point: (worldPoint) => ({
          x: centreX + worldPoint.x * scale,
          y: centreY - worldPoint.y * scale
        })
      };
    }

    function drawWorldLine(line, projector, colour, lineWidth, dash) {
      const [a, b, c] = line;
      const magnitudeSquared = a * a + b * b;
      if (magnitudeSquared < 1e-12) return;
      const origin = { x: -a * c / magnitudeSquared, y: -b * c / magnitudeSquared };
      const inverseMagnitude = 1 / Math.sqrt(magnitudeSquared);
      const direction = { x: b * inverseMagnitude, y: -a * inverseMagnitude };
      const extent = 12;
      const start = projector.point({ x: origin.x - direction.x * extent, y: origin.y - direction.y * extent });
      const end = projector.point({ x: origin.x + direction.x * extent, y: origin.y + direction.y * extent });
      context.save();
      context.strokeStyle = colour;
      context.lineWidth = lineWidth;
      context.setLineDash(dash || []);
      context.beginPath();
      context.moveTo(start.x, start.y);
      context.lineTo(end.x, end.y);
      context.stroke();
      context.restore();
    }

    function drawEllipse(projector) {
      context.save();
      context.strokeStyle = "rgba(83, 207, 219, 0.23)";
      context.lineWidth = 1;
      context.setLineDash([3, 9]);
      context.beginPath();
      for (let index = 0; index <= 240; index += 1) {
        const point = projector.point(pointOnEllipse(TAU * index / 240));
        if (index === 0) context.moveTo(point.x, point.y);
        else context.lineTo(point.x, point.y);
      }
      context.closePath();
      context.stroke();
      context.restore();
    }

    function drawHexagon(points, projector) {
      context.save();
      context.strokeStyle = "rgba(130, 240, 207, 0.24)";
      context.lineWidth = 0.9;
      context.beginPath();
      points.forEach((worldPoint, index) => {
        const point = projector.point(worldPoint);
        if (index === 0) context.moveTo(point.x, point.y);
        else context.lineTo(point.x, point.y);
      });
      context.closePath();
      context.stroke();
      context.restore();
    }

    function drawConicPoint(worldPoint, label, projector) {
      const point = projector.point(worldPoint);
      context.save();
      context.fillStyle = "rgba(227, 248, 240, 0.92)";
      context.shadowColor = "rgba(130, 240, 207, 0.7)";
      context.shadowBlur = 11;
      context.beginPath();
      context.arc(point.x, point.y, 2.6, 0, TAU);
      context.fill();
      context.shadowBlur = 0;
      context.fillStyle = "rgba(184, 221, 208, 0.66)";
      context.font = "8px ui-monospace, SFMono-Regular, Consolas, monospace";
      context.textAlign = worldPoint.x < 0 ? "right" : "left";
      context.fillText(label, point.x + (worldPoint.x < 0 ? -8 : 8), point.y - 7);
      context.restore();
    }

    function drawIntersection(worldPoint, label, projector) {
      const point = projector.point(worldPoint);
      context.save();
      context.strokeStyle = "rgba(231, 185, 92, 0.78)";
      context.fillStyle = "rgba(255, 238, 198, 0.9)";
      context.shadowColor = "rgba(231, 185, 92, 0.62)";
      context.shadowBlur = 13;
      context.lineWidth = 1;
      context.beginPath();
      context.arc(point.x, point.y, 4.2, 0, TAU);
      context.stroke();
      context.beginPath();
      context.arc(point.x, point.y, 1.45, 0, TAU);
      context.fill();
      context.shadowBlur = 0;
      context.fillStyle = "rgba(244, 213, 145, 0.76)";
      context.font = "700 8px ui-monospace, SFMono-Regular, Consolas, monospace";
      context.textAlign = "left";
      context.fillText(label, point.x + 8, point.y - 7);
      context.restore();
    }

    function drawCaption(geometry) {
      const right = Math.max(22, width * 0.035);
      const top = Math.max(28, height * 0.075);
      context.save();
      context.textAlign = "right";
      context.fillStyle = "rgba(231, 185, 92, 0.54)";
      context.font = "7px ui-monospace, SFMono-Regular, Consolas, monospace";
      context.fillText("PASCAL · SIX POINTS / ONE LINE", width - right, top);
      context.fillStyle = "rgba(174, 207, 195, 0.43)";
      context.font = "6px ui-monospace, SFMono-Regular, Consolas, monospace";
      context.fillText("X = AB ∩ DE   ·   Y = BC ∩ EF   ·   Z = CD ∩ FA", width - right, top + 16);
      context.fillStyle = "rgba(130, 240, 207, 0.39)";
      context.fillText(`COLLINEARITY RESIDUAL · ${Math.max(geometry.collinearityError, Number.EPSILON).toExponential(1)}`, width - right, top + 31);
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
      canvas.dataset.intersections = "X,Y,Z";
      canvas.dataset.collinearityError = geometry.collinearityError.toExponential(3);

      context.save();
      context.globalAlpha = width < 600 ? 0.58 : 0.72;
      drawEllipse(projector);
      drawWorldLine(geometry.sides[0], projector, "rgba(83, 207, 219, 0.075)", 0.7, [5, 12]);
      drawWorldLine(geometry.sides[3], projector, "rgba(83, 207, 219, 0.075)", 0.7, [5, 12]);
      drawWorldLine(geometry.sides[1], projector, "rgba(231, 185, 92, 0.07)", 0.7, [3, 13]);
      drawWorldLine(geometry.sides[4], projector, "rgba(231, 185, 92, 0.07)", 0.7, [3, 13]);
      drawWorldLine(geometry.sides[2], projector, "rgba(168, 137, 224, 0.065)", 0.7, [2, 11]);
      drawWorldLine(geometry.sides[5], projector, "rgba(168, 137, 224, 0.065)", 0.7, [2, 11]);
      drawHexagon(geometry.points, projector);

      context.save();
      context.shadowColor = "rgba(231, 185, 92, 0.38)";
      context.shadowBlur = 9;
      drawWorldLine(geometry.pascalLine, projector, "rgba(231, 185, 92, 0.47)", 1.15);
      context.restore();

      geometry.points.forEach((point, index) => drawConicPoint(point, POINT_LABELS[index], projector));
      geometry.intersections.forEach((point, index) => drawIntersection(point, ["X", "Y", "Z"][index], projector));
      drawCaption(geometry);
      context.restore();
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

    function handleVisibility() {
      updatePlayback();
    }

    function handleMotionPreference() {
      updatePlayback();
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

    document.addEventListener("visibilitychange", handleVisibility);
    if (typeof reducedMotion.addEventListener === "function") reducedMotion.addEventListener("change", handleMotionPreference);
    else reducedMotion.addListener(handleMotionPreference);

    const api = {
      render,
      getState: () => ({
        running: shouldRun(),
        reducedMotion: reducedMotion.matches,
        inViewport,
        elapsed,
        collinearityError: canvas.dataset.collinearityError || null
      }),
      destroy: () => {
        if (destroyed) return;
        destroyed = true;
        window.cancelAnimationFrame(animationFrame);
        document.removeEventListener("visibilitychange", handleVisibility);
        if (typeof reducedMotion.removeEventListener === "function") reducedMotion.removeEventListener("change", handleMotionPreference);
        else reducedMotion.removeListener(handleMotionPreference);
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
