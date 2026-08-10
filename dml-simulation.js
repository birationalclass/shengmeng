window.createDmlHeroSimulation = () => {
  const backgroundCanvas = document.querySelector("#algebraicDynamics");
  const returnCanvas = document.querySelector("#parameterDynamics");
  if (!backgroundCanvas || !returnCanvas) return;

  const backgroundContext = backgroundCanvas.getContext("2d", { alpha: true });
  const returnContext = returnCanvas.getContext("2d", { alpha: true });
  if (!backgroundContext || !returnContext) return;

  let context = backgroundContext;
  const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");
  const fullTurn = Math.PI * 2;
  const cycleDuration = 60;
  const secondsPerIteration = 0.75;
  const targetAxisX = 0.62;
  const targetAxisY = 0.48;
  const targetRadialAmplitude = 0.22;
  const targetRotation = -0.14;
  const intersectionAngle = Math.PI / 4;
  const clamp = (value, minimum, maximum) => Math.max(minimum, Math.min(maximum, value));
  const positiveModulo = (value, modulus) => ((value % modulus) + modulus) % modulus;

  const rotatePoint = (point, angle) => ({
    x: point.x * Math.cos(angle) - point.y * Math.sin(angle),
    y: point.x * Math.sin(angle) + point.y * Math.cos(angle)
  });
  const targetCurve = (parameter) => {
    const cosine = Math.cos(parameter);
    const sine = Math.sin(parameter);
    const sineTriple = 3 * sine - 4 * Math.pow(sine, 3);
    const cosineQuintuple = 16 * Math.pow(cosine, 5) - 20 * Math.pow(cosine, 3) + 5 * cosine;
    const asymmetricWeight = 1 + 0.28 * cosine - 0.18 * sineTriple + 0.10 * cosineQuintuple;
    const radialScale = 1
      + targetRadialAmplitude * (cosine * cosine - sine * sine) * asymmetricWeight;
    return rotatePoint({
      x: targetAxisX * radialScale * cosine,
      y: targetAxisY * radialScale * sine
    }, targetRotation);
  };

  const ellipseSpecs = [
    [16, 0, "DYNAMICS I"],
    [24, 2, "DYNAMICS II"],
    [32, 3, "DYNAMICS III"],
    [40, 1, "DYNAMICS IV"],
    [16, 4, "DYNAMICS V"],
    [24, 5, "DYNAMICS VI"],
    [32, 7, "DYNAMICS VII"],
    [40, 8, "DYNAMICS VIII"],
    [16, 1, "DYNAMICS IX"],
    [24, 4, "DYNAMICS X"]
  ];

  const orbitSets = ellipseSpecs.map(([modulus, offsetSteps, label]) => {
    const stepAngle = fullTurn / modulus;
    const offsetAngle = offsetSteps * stepAngle;
    const hitParameterIndices = [modulus / 8, (3 * modulus) / 8, (5 * modulus) / 8, (7 * modulus) / 8];
    const hitParameters = [
      intersectionAngle,
      3 * intersectionAngle,
      5 * intersectionAngle,
      7 * intersectionAngle
    ];
    const hits = hitParameterIndices
      .map((index, hitIndex) => ({
        parameter: hitParameters[hitIndex],
        residue: positiveModulo(index - offsetSteps, modulus)
      }))
      .sort((first, second) => first.residue - second.residue);
    const residues = hits.map((hit) => hit.residue);
    const movingCurve = (parameter) => rotatePoint({
      x: targetAxisX * Math.cos(parameter),
      y: targetAxisY * Math.sin(parameter)
    }, targetRotation);
    return {
      majorAxis: targetAxisX,
      minorAxis: targetAxisY,
      rotation: targetRotation,
      modulus,
      offsetAngle,
      stepAngle,
      residues,
      hits,
      movingCurve,
      label
    };
  });

  let width = 1;
  let height = 1;
  let backgroundWidth = 1;
  let backgroundHeight = 1;
  let returnWidth = 1;
  let returnHeight = 1;
  let active = true;
  let inViewport = true;
  let animationFrame = 0;
  let previousFrame = 0;
  let elapsed = 0;

  [backgroundCanvas, returnCanvas].forEach((target) => {
    target.dataset.orbitSets = String(orbitSets.length);
    target.dataset.target = "V: asymmetric polynomial image of the unit circle";
  });

  function fitCanvas(target, targetContext) {
    const bounds = target.getBoundingClientRect();
    const pixelRatio = Math.min(window.devicePixelRatio || 1, 2);
    const fittedWidth = Math.max(1, bounds.width);
    const fittedHeight = Math.max(1, bounds.height);
    target.width = Math.round(fittedWidth * pixelRatio);
    target.height = Math.round(fittedHeight * pixelRatio);
    targetContext.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);
    return { width: fittedWidth, height: fittedHeight };
  }

  function resizeCanvases() {
    const backgroundSize = fitCanvas(backgroundCanvas, backgroundContext);
    const returnSize = fitCanvas(returnCanvas, returnContext);
    backgroundWidth = backgroundSize.width;
    backgroundHeight = backgroundSize.height;
    returnWidth = returnSize.width;
    returnHeight = returnSize.height;
    render(elapsed);
  }

  function pointInFrame(point, frame) {
    return {
      x: frame.left + ((point.x + 1) / 2) * frame.size,
      y: frame.top + (1 - (point.y + 1) / 2) * frame.size
    };
  }

  function drawCompleteCurve(curve, frame, colour, lineWidth = 0.9) {
    context.save();
    context.strokeStyle = colour;
    context.lineWidth = lineWidth;
    context.beginPath();
    for (let index = 0; index <= 280; index += 1) {
      const point = pointInFrame(curve((fullTurn * index) / 280), frame);
      if (index === 0) context.moveTo(point.x, point.y);
      else context.lineTo(point.x, point.y);
    }
    context.stroke();
    context.restore();
  }

  function drawTrail(curve, parameterAtTime, time, frame, colour) {
    const segments = width < 400 ? 52 : 70;
    const step = 0.04;
    context.save();
    context.globalCompositeOperation = "lighter";
    for (let index = 1; index <= segments; index += 1) {
      const older = pointInFrame(curve(parameterAtTime(time - index * step)), frame);
      const newer = pointInFrame(curve(parameterAtTime(time - (index - 1) * step)), frame);
      const life = 1 - index / segments;
      context.strokeStyle = colour.replace("ALPHA", String(0.03 + 0.56 * life * life));
      context.lineWidth = 0.5 + life * 1.2;
      context.beginPath();
      context.moveTo(older.x, older.y);
      context.lineTo(newer.x, newer.y);
      context.stroke();
    }
    context.restore();
  }

  function drawParticle(point, colour, coreColour, emphasis = 0) {
    context.save();
    context.globalCompositeOperation = "lighter";
    const haloRadius = 15 + emphasis * 13;
    const halo = context.createRadialGradient(point.x, point.y, 0, point.x, point.y, haloRadius);
    halo.addColorStop(0, colour.replace("ALPHA", String(0.46 + emphasis * 0.34)));
    halo.addColorStop(0.24, colour.replace("ALPHA", String(0.17 + emphasis * 0.14)));
    halo.addColorStop(1, colour.replace("ALPHA", "0"));
    context.fillStyle = halo;
    context.beginPath();
    context.arc(point.x, point.y, haloRadius, 0, fullTurn);
    context.fill();
    context.fillStyle = coreColour;
    context.beginPath();
    context.arc(point.x, point.y, 2.2 + emphasis * 1.2, 0, fullTurn);
    context.fill();
    context.restore();
  }

  function iterationDistance(iteration, residue, modulus) {
    const remainder = positiveModulo(iteration - residue, modulus);
    return Math.min(remainder, modulus - remainder);
  }

  function drawHitLocus(frame, set, iteration) {
    context.save();
    set.hits.forEach((hit) => {
      const point = pointInFrame(set.movingCurve(hit.parameter), frame);
      const distance = iterationDistance(iteration, hit.residue, set.modulus);
      const pulse = Math.exp(-Math.pow(distance / 0.18, 2));
      context.strokeStyle = `rgba(231, 185, 92, ${0.24 + pulse * 0.64})`;
      context.lineWidth = 0.8 + pulse * 1.2;
      context.beginPath();
      context.arc(point.x, point.y, 2.5 + pulse * 8, 0, fullTurn);
      context.stroke();
    });
    context.restore();
  }

  function drawLabel(text, x, y, colour = "rgba(202, 222, 214, 0.62)", size = 8) {
    context.save();
    context.fillStyle = colour;
    context.font = `${size}px ui-monospace, SFMono-Regular, Consolas, monospace`;
    context.fillText(text, x, y);
    context.restore();
  }

  function returnRecords(set, currentIteration) {
    return set.residues.map((residue) => {
      const records = [];
      for (let iteration = residue; iteration <= currentIteration + 1e-7; iteration += set.modulus) {
        records.push(iteration);
      }
      return { residue, records };
    });
  }

  function returnPoint(iteration, lane, frame, nLimit, laneCount) {
    return {
      x: frame.left + (iteration / nLimit) * frame.width,
      y: frame.top + ((lane + 0.5) / laneCount) * frame.height
    };
  }

  function drawReturnPlane(frame, set, lanes, currentIteration, nLimit) {
    const divisions = 4;
    context.save();
    context.font = "5.5px ui-monospace, SFMono-Regular, Consolas, monospace";
    context.lineWidth = 0.7;

    for (let index = 0; index <= divisions; index += 1) {
      const x = frame.left + (frame.width * index) / divisions;
      context.strokeStyle = index === 0 || index === divisions
        ? "rgba(130, 240, 207, 0.14)"
        : "rgba(130, 240, 207, 0.065)";
      context.beginPath();
      context.moveTo(x, frame.top);
      context.lineTo(x, frame.top + frame.height);
      context.stroke();
      context.fillStyle = "rgba(180, 207, 197, 0.42)";
      context.textAlign = "center";
      context.fillText(String(Math.round((nLimit * index) / divisions)), x, frame.top + frame.height + 11);
    }

    lanes.forEach((lane, laneIndex) => {
      const y = frame.top + ((laneIndex + 0.5) / lanes.length) * frame.height;
      context.strokeStyle = "rgba(130, 240, 207, 0.065)";
      context.beginPath();
      context.moveTo(frame.left, y);
      context.lineTo(frame.left + frame.width, y);
      context.stroke();
      context.fillStyle = "rgba(202, 222, 214, 0.54)";
      context.textAlign = "right";
      context.fillText(`r=${lane.residue}`, frame.left - 7, y + 2);

      if (lane.records.length >= 2) {
        const start = returnPoint(lane.records[0], laneIndex, frame, nLimit, lanes.length);
        const end = returnPoint(lane.records[lane.records.length - 1], laneIndex, frame, nLimit, lanes.length);
        context.strokeStyle = "rgba(130, 240, 207, 0.34)";
        context.lineWidth = 0.9;
        context.beginPath();
        context.moveTo(start.x, start.y);
        context.lineTo(end.x, end.y);
        context.stroke();

        const second = returnPoint(lane.records[1], laneIndex, frame, nLimit, lanes.length);
        const bracketY = start.y - 8;
        context.strokeStyle = "rgba(231, 185, 92, 0.42)";
        context.beginPath();
        context.moveTo(start.x, bracketY + 3);
        context.lineTo(start.x, bracketY);
        context.lineTo(second.x, bracketY);
        context.lineTo(second.x, bracketY + 3);
        context.stroke();
        context.fillStyle = "rgba(231, 185, 92, 0.66)";
        context.textAlign = "center";
        context.fillText(`Δn=${set.modulus}`, (start.x + second.x) / 2, bracketY - 2);
      }

      lane.records.forEach((iteration) => {
        const point = returnPoint(iteration, laneIndex, frame, nLimit, lanes.length);
        const recent = currentIteration - iteration < 0.32;
        context.fillStyle = recent ? "rgba(255, 244, 215, 0.98)" : "rgba(130, 240, 207, 0.88)";
        context.beginPath();
        context.arc(point.x, point.y, recent ? 2.4 : 1.5, 0, fullTurn);
        context.fill();
      });
    });

    const nowX = frame.left + (Math.min(currentIteration, nLimit) / nLimit) * frame.width;
    context.setLineDash([2, 3]);
    context.strokeStyle = "rgba(231, 185, 92, 0.25)";
    context.beginPath();
    context.moveTo(nowX, frame.top);
    context.lineTo(nowX, frame.top + frame.height);
    context.stroke();
    context.setLineDash([]);
    context.fillStyle = "rgba(202, 222, 214, 0.6)";
    context.textAlign = "left";
    context.fillText("n", frame.left + frame.width + 5, frame.top + frame.height + 2);
    context.restore();
  }

  function render(time) {
    const cycleNumber = Math.floor(time / cycleDuration);
    const cycleTime = time % cycleDuration;
    const setIndex = cycleNumber % orbitSets.length;
    const set = orbitSets[setIndex];
    const resetIn = cycleDuration - Math.floor(cycleTime);
    const currentIteration = cycleTime / secondsPerIteration;
    const ellipseParameter = set.offsetAngle + currentIteration * set.stepAngle;
    const lanes = returnRecords(set, currentIteration);
    const hitCount = lanes.reduce((total, lane) => total + lane.records.length, 0);
    const nLimit = Math.max(set.modulus + 2, Math.min(cycleDuration / secondsPerIteration, currentIteration + 3));
    const hitDistance = Math.min(...set.residues.map((residue) => iterationDistance(currentIteration, residue, set.modulus)));
    const hitEmphasis = Math.exp(-Math.pow(hitDistance / 0.18, 2));

    [backgroundCanvas, returnCanvas].forEach((target) => {
      target.dataset.orbitSet = String(setIndex + 1);
      target.dataset.movingOrbit = set.label;
      target.dataset.modulus = String(set.modulus);
      target.dataset.residues = set.residues.join(",");
    });
    returnCanvas.dataset.iteration = currentIteration.toFixed(2);
    returnCanvas.dataset.hitCount = String(hitCount);
    returnCanvas.dataset.progressions = String(set.residues.length);
    returnCanvas.dataset.commonDifference = String(set.modulus);
    returnCanvas.dataset.resetIn = String(resetIn);

    context = backgroundContext;
    width = backgroundWidth;
    height = backgroundHeight;
    context.clearRect(0, 0, width, height);
    const narrow = width < 700;
    const plotSize = Math.max(340, Math.min(width * (narrow ? 1.55 : 1.03), height * (narrow ? 0.76 : 1.22)));
    const plotCentreX = width * (narrow ? 0.56 : 0.62);
    const plotCentreY = height * (narrow ? 0.54 : 0.52);
    const plotFrame = {
      left: plotCentreX - plotSize / 2,
      top: plotCentreY - plotSize / 2,
      size: plotSize
    };
    drawCompleteCurve(targetCurve, plotFrame, "rgba(83, 207, 219, 0.24)", 1.05);
    drawCompleteCurve(set.movingCurve, plotFrame, "rgba(231, 185, 92, 0.18)", 0.9);
    drawHitLocus(plotFrame, set, currentIteration);
    drawTrail(
      set.movingCurve,
      (trailTime) => set.offsetAngle + (trailTime / secondsPerIteration) * set.stepAngle,
      cycleTime,
      plotFrame,
      "rgba(231, 185, 92, ALPHA)"
    );
    drawParticle(pointInFrame(set.movingCurve(ellipseParameter), plotFrame), "rgba(231, 185, 92, ALPHA)", "rgba(255, 244, 215, 0.98)", hitEmphasis);

    if (!narrow) {
      drawLabel("V · FIXED ASYMMETRIC POLYNOMIAL LOOP", clamp(plotFrame.left + 34, 28, width - 340), height - 42, "rgba(83, 207, 219, 0.4)", 7);
      drawLabel(`b_n · ${set.label}`, clamp(plotFrame.left + 300, 290, width - 240), height - 42, "rgba(231, 185, 92, 0.38)", 7);
    }

    context = returnContext;
    width = returnWidth;
    height = returnHeight;
    context.clearRect(0, 0, width, height);
    const returnFrame = {
      left: 58,
      top: 84,
      width: Math.max(150, width - 84),
      height: Math.max(132, height - 142)
    };
    const residueSet = `{${set.residues.join(",")}}`;
    drawLabel(`DYNAMICAL MORDELL–LANG · SET ${String(setIndex + 1).padStart(2, "0")}/${orbitSets.length}`, 27, 26, "rgba(231, 185, 92, 0.78)", 6.6);
    drawLabel("N_V = { n ≥ 0 : b_n ∈ V }", 27, 42, "rgba(202, 222, 214, 0.62)", 6.2);
    drawLabel(`N_V = ⋃ (r + ${set.modulus}ℕ),  r ∈ ${residueSet}`, 27, 58, "rgba(130, 240, 207, 0.7)", 6.1);
    drawLabel(`${hitCount} RETURNS · ${set.residues.length} ARITHMETIC PROGRESSIONS`, 27, 72, "rgba(202, 222, 214, 0.48)", 5.8);
    drawReturnPlane(returnFrame, set, lanes, currentIteration, nLimit);
    drawLabel(`n ≤ ${Math.floor(currentIteration)} · Δn = ${set.modulus} · RESET ${resetIn}s`, returnFrame.left, height - 23, "rgba(231, 185, 92, 0.56)", 6.1);
  }

  function animate(timestamp) {
    if (!previousFrame) previousFrame = timestamp;
    elapsed += Math.min((timestamp - previousFrame) / 1000, 0.05);
    previousFrame = timestamp;
    render(elapsed);
    if (active && !reducedMotion.matches) animationFrame = requestAnimationFrame(animate);
  }

  function setActive(nextActive) {
    active = nextActive && !document.hidden;
    cancelAnimationFrame(animationFrame);
    if (active && !reducedMotion.matches) {
      previousFrame = 0;
      animationFrame = requestAnimationFrame(animate);
    } else {
      render(reducedMotion.matches ? 20 : elapsed);
    }
  }

  const resizeObserver = new ResizeObserver(resizeCanvases);
  resizeObserver.observe(backgroundCanvas);
  resizeObserver.observe(returnCanvas);
  const visibilityObserver = new IntersectionObserver(([entry]) => {
    inViewport = entry.isIntersecting;
    setActive(inViewport);
  }, { threshold: 0.02 });
  visibilityObserver.observe(backgroundCanvas);
  document.addEventListener("visibilitychange", () => setActive(inViewport));
  reducedMotion.addEventListener("change", () => setActive(inViewport));
  resizeCanvases();
  setActive(true);
};
