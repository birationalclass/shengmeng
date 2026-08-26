(() => {
  "use strict";

  const canvas = document.querySelector("#gluingCanvas");
  const context = canvas.getContext("2d");
  const degreeButtons = [...document.querySelectorAll("[data-degree]")];
  const degreeOutput = document.querySelector("#degreeOutput");
  const degreeDescription = document.querySelector("#degreeDescription");
  const playToggle = document.querySelector("#playToggle");
  const playLabel = document.querySelector("#playLabel");
  const positionControl = document.querySelector("#positionControl");
  const positionRange = document.querySelector("#positionRange");
  const positionOutput = document.querySelector("#positionOutput");
  const speedRange = document.querySelector("#speedRange");
  const speedOutput = document.querySelector("#speedOutput");
  const sectionsToggle = document.querySelector("#sectionsToggle");
  const surfaceName = document.querySelector("#surfaceName");
  const formulaDegree = document.querySelector("#formulaDegree");
  const trackerDegree = document.querySelector("#trackerDegree");
  const twistStatus = document.querySelector("#twistStatus");
  const transitionPower = document.querySelector("#transitionPower");
  const phaseFormula = document.querySelector("#phaseFormula");
  const formulaExplanation = document.querySelector("#formulaExplanation");
  const angleReadout = document.querySelector("#angleReadout");
  const phaseReadout = document.querySelector("#phaseReadout");
  const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");

  const palette = {
    paper: "#e8f2ed",
    muted: "#8ca49b",
    mint: "#82f0cf",
    cyan: "#53cfdb",
    gold: "#e7b95c",
    rose: "#ef83a8",
    violet: "#a997ef",
    ink: "#071513"
  };

  const subscripts = ["₀", "₁", "₂", "₃", "₄"];
  const state = {
    degree: 1,
    manualPosition: 0.16,
    isPlaying: !reducedMotion.matches,
    speed: 0.16,
    showSections: true,
    anchorPosition: 0.16,
    anchorTime: performance.now(),
    width: 0,
    height: 0,
    animationFrame: 0
  };

  function wrapUnit(value) {
    return ((value % 1) + 1) % 1;
  }

  function currentPosition(now = performance.now()) {
    if (!state.isPlaying) return state.manualPosition;
    return wrapUnit(state.anchorPosition + ((now - state.anchorTime) / 1000) * state.speed);
  }

  function setPaused(paused) {
    if (paused === !state.isPlaying) return;

    if (paused) {
      state.manualPosition = currentPosition();
      state.isPlaying = false;
      cancelAnimationFrame(state.animationFrame);
      state.animationFrame = 0;
      render(state.manualPosition);
    } else {
      state.anchorPosition = state.manualPosition;
      state.anchorTime = performance.now();
      state.isPlaying = true;
      requestTick();
    }
    updateMotionUI();
  }

  function updateMotionUI() {
    playToggle.setAttribute("aria-pressed", String(state.isPlaying));
    playLabel.textContent = state.isPlaying ? "Pause" : "Play";
    positionControl.hidden = state.isPlaying;
    positionRange.value = state.manualPosition.toFixed(3);
    speedRange.value = state.speed.toFixed(2);
    speedOutput.textContent = `${state.speed.toFixed(2)}×`;
    updateReadouts(currentPosition());
  }

  function updateDegreeUI() {
    const n = state.degree;
    degreeButtons.forEach((button) => {
      button.setAttribute("aria-pressed", String(Number(button.dataset.degree) === n));
    });

    degreeOutput.textContent = `n = ${n}`;
    surfaceName.textContent = `𝔽${subscripts[n]}`;
    formulaDegree.textContent = String(n);
    trackerDegree.textContent = `n=${n}`;
    transitionPower.textContent = String(n);
    phaseFormula.textContent = String(n);
    canvas.setAttribute("aria-label", `Animated gluing diagram for the Hirzebruch surface F ${n}`);

    if (n === 0) {
      degreeDescription.textContent = "F₀ = P¹ × P¹: the two charts agree without twisting.";
      twistStatus.classList.add("product");
      twistStatus.querySelector("span").textContent = "product";
      formulaExplanation.textContent = "The gold band is the overlap. The moving mint frame is described first in U₀, then re-expressed in U∞. For n = 0 it returns unchanged.";
    } else {
      const turns = n === 1 ? "once" : `${n} times`;
      degreeDescription.textContent = `F${subscripts[n]} = P(O ⊕ O(${n})). The frame winds ${turns} around the overlap.`;
      twistStatus.classList.remove("product");
      twistStatus.querySelector("span").textContent = n === 1 ? "one twist" : `${n} twists`;
      formulaExplanation.textContent = `The gold band is the overlap. The moving mint frame is described first in U₀, then re-expressed in U∞. For n = ${n} it makes ${n === 1 ? "one full turn" : `${n} full turns`}.`;
    }
  }

  function updateReadouts(position) {
    const angle = Math.round(wrapUnit(position) * 360) % 360;
    const phase = state.degree * angle;
    positionOutput.textContent = `${angle}°`;
    angleReadout.textContent = `θ = ${angle}°`;
    phaseReadout.textContent = `nθ = ${phase}°`;
  }

  function resizeCanvas() {
    const rect = canvas.getBoundingClientRect();
    if (!rect.width || !rect.height) return;

    const scale = Math.min(window.devicePixelRatio || 1, 2);
    const nextWidth = Math.round(rect.width * scale);
    const nextHeight = Math.round(rect.height * scale);
    if (canvas.width !== nextWidth || canvas.height !== nextHeight) {
      canvas.width = nextWidth;
      canvas.height = nextHeight;
    }
    context.setTransform(scale, 0, 0, scale, 0, 0);
    state.width = rect.width;
    state.height = rect.height;
    render(currentPosition());
  }

  function roundedRectPath(ctx, x, y, width, height, radius) {
    const r = Math.min(radius, width / 2, height / 2);
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + width, y, x + width, y + height, r);
    ctx.arcTo(x + width, y + height, x, y + height, r);
    ctx.arcTo(x, y + height, x, y, r);
    ctx.arcTo(x, y, x + width, y, r);
    ctx.closePath();
  }

  function basePoint(q, geometry) {
    return {
      x: geometry.left + (geometry.right - geometry.left) * q,
      y: geometry.baseY + Math.sin(2 * Math.PI * q) * geometry.baseWave
    };
  }

  function traceCurve(callback, samples = 180) {
    context.beginPath();
    for (let index = 0; index <= samples; index += 1) {
      const point = callback(index / samples);
      if (index === 0) context.moveTo(point.x, point.y);
      else context.lineTo(point.x, point.y);
    }
  }

  function line(x1, y1, x2, y2) {
    context.beginPath();
    context.moveTo(x1, y1);
    context.lineTo(x2, y2);
    context.stroke();
  }

  function drawChartRegions(geometry) {
    const midpoint = (geometry.left + geometry.right) / 2;
    const top = geometry.top;
    const bottom = geometry.bottom;
    const seamWidth = geometry.seamWidth;

    const leftGradient = context.createLinearGradient(geometry.left, top, midpoint, bottom);
    leftGradient.addColorStop(0, "rgba(83, 207, 219, .082)");
    leftGradient.addColorStop(1, "rgba(83, 207, 219, .025)");
    roundedRectPath(context, geometry.left, top, midpoint - geometry.left + seamWidth / 2, bottom - top, 14);
    context.fillStyle = leftGradient;
    context.fill();
    context.strokeStyle = "rgba(83, 207, 219, .11)";
    context.lineWidth = 1;
    context.stroke();

    const rightGradient = context.createLinearGradient(midpoint, top, geometry.right, bottom);
    rightGradient.addColorStop(0, "rgba(169, 151, 239, .025)");
    rightGradient.addColorStop(1, "rgba(169, 151, 239, .075)");
    roundedRectPath(context, midpoint - seamWidth / 2, top, geometry.right - midpoint + seamWidth / 2, bottom - top, 14);
    context.fillStyle = rightGradient;
    context.fill();
    context.strokeStyle = "rgba(169, 151, 239, .11)";
    context.stroke();

    const overlapGradient = context.createLinearGradient(midpoint - seamWidth / 2, 0, midpoint + seamWidth / 2, 0);
    overlapGradient.addColorStop(0, "rgba(231, 185, 92, .035)");
    overlapGradient.addColorStop(.5, "rgba(231, 185, 92, .16)");
    overlapGradient.addColorStop(1, "rgba(231, 185, 92, .035)");
    roundedRectPath(context, midpoint - seamWidth / 2, top, seamWidth, bottom - top, 10);
    context.fillStyle = overlapGradient;
    context.fill();
    context.strokeStyle = "rgba(231, 185, 92, .18)";
    context.stroke();
  }

  function drawBase(geometry) {
    context.save();
    traceCurve((q) => basePoint(q, geometry));
    context.strokeStyle = "rgba(232, 242, 237, .74)";
    context.lineWidth = 2.1;
    context.lineCap = "round";
    context.shadowColor = "rgba(232, 242, 237, .13)";
    context.shadowBlur = 8;
    context.stroke();
    context.shadowBlur = 0;

    for (let index = 0; index <= 8; index += 1) {
      const point = basePoint(index / 8, geometry);
      context.beginPath();
      context.arc(point.x, point.y, 2.1, 0, Math.PI * 2);
      context.fillStyle = "rgba(140, 164, 155, .72)";
      context.fill();
    }
    context.restore();
  }

  function drawRuledSurface(geometry) {
    const n = state.degree;
    context.save();

    if (state.showSections) {
      [-1, 1].forEach((sign) => {
        traceCurve((q) => {
          const point = basePoint(q, geometry);
          return {
            x: point.x,
            y: point.y - geometry.fiberHeight * (0.5 + sign * 0.18 * Math.sin(2 * Math.PI * n * q))
          };
        });
        context.strokeStyle = sign > 0 ? "rgba(130, 240, 207, .82)" : "rgba(239, 131, 168, .7)";
        context.lineWidth = 2.2;
        context.shadowColor = sign > 0 ? "rgba(130, 240, 207, .18)" : "rgba(239, 131, 168, .13)";
        context.shadowBlur = 8;
        context.stroke();
      });
    }

    context.shadowBlur = 0;
    for (let index = 0; index <= 24; index += 1) {
      const q = index / 24;
      const base = basePoint(q, geometry);
      const phase = 2 * Math.PI * n * q;
      const top = {
        x: base.x + Math.cos(phase) * geometry.fiberHeight * 0.1,
        y: base.y - geometry.fiberHeight * (0.44 + 0.16 * Math.sin(phase))
      };
      context.strokeStyle = index % 4 === 0 ? "rgba(83, 207, 219, .32)" : "rgba(83, 207, 219, .18)";
      context.lineWidth = index % 4 === 0 ? 1.25 : .85;
      line(base.x, base.y, top.x, top.y);

      context.beginPath();
      context.arc(top.x, top.y, index % 4 === 0 ? 1.8 : 1.15, 0, Math.PI * 2);
      context.fillStyle = "rgba(83, 207, 219, .48)";
      context.fill();
    }
    context.restore();
  }

  function drawGluingWindow(geometry) {
    const midpoint = (geometry.left + geometry.right) / 2;
    const q0 = 0.435;
    const q1 = 0.565;
    const p0 = basePoint(q0, geometry);
    const p1 = basePoint(q1, geometry);
    const theta0 = 2 * Math.PI * state.degree * q0;
    const theta1 = 2 * Math.PI * state.degree * q1;
    const a = {
      x: p0.x + Math.cos(theta0) * geometry.fiberHeight * 0.1,
      y: p0.y - geometry.fiberHeight * (0.44 + 0.16 * Math.sin(theta0))
    };
    const b = {
      x: p1.x + Math.cos(theta1) * geometry.fiberHeight * 0.1,
      y: p1.y - geometry.fiberHeight * (0.44 + 0.16 * Math.sin(theta1))
    };

    context.save();
    context.beginPath();
    context.moveTo(p0.x, p0.y);
    context.lineTo(a.x, a.y);
    context.lineTo(b.x, b.y);
    context.lineTo(p1.x, p1.y);
    context.closePath();
    context.fillStyle = "rgba(231, 185, 92, .11)";
    context.fill();
    context.strokeStyle = "rgba(231, 185, 92, .87)";
    context.lineWidth = 1.8;
    context.shadowColor = "rgba(231, 185, 92, .18)";
    context.shadowBlur = 8;
    context.stroke();
    context.shadowBlur = 0;

    const arrowY = geometry.top + Math.max(47, geometry.height * .075);
    const halfArrow = geometry.seamWidth * .33;
    context.strokeStyle = "rgba(231, 185, 92, .82)";
    context.lineWidth = 1.4;
    line(midpoint - halfArrow, arrowY, midpoint + halfArrow, arrowY);
    line(midpoint + halfArrow, arrowY, midpoint + halfArrow - 6, arrowY - 4);
    line(midpoint + halfArrow, arrowY, midpoint + halfArrow - 6, arrowY + 4);

    context.fillStyle = palette.gold;
    context.font = `700 ${geometry.labelSmall}px ${getComputedStyle(document.body).fontFamily}`;
    context.textAlign = "center";
    context.textBaseline = "middle";
    context.fillText(`multiply by z^${state.degree}`, midpoint, arrowY - 18);
    context.restore();
  }

  function drawArrow(from, to, color, width) {
    context.save();
    const angle = Math.atan2(to.y - from.y, to.x - from.x);
    const headSize = 8;
    context.strokeStyle = color;
    context.lineWidth = width;
    context.lineCap = "round";
    context.lineJoin = "round";
    context.beginPath();
    context.moveTo(from.x, from.y);
    context.lineTo(to.x, to.y);
    context.stroke();
    context.beginPath();
    context.moveTo(to.x, to.y);
    context.lineTo(to.x - Math.cos(angle - Math.PI / 6) * headSize, to.y - Math.sin(angle - Math.PI / 6) * headSize);
    context.moveTo(to.x, to.y);
    context.lineTo(to.x - Math.cos(angle + Math.PI / 6) * headSize, to.y - Math.sin(angle + Math.PI / 6) * headSize);
    context.stroke();
    context.restore();
  }

  function drawMovingFiber(geometry, q) {
    const point = basePoint(q, geometry);
    const phase = 2 * Math.PI * state.degree * q;
    const length = geometry.fiberHeight * 0.58;
    const tip = {
      x: point.x + Math.cos(phase) * length * 0.45,
      y: point.y - length * (0.52 + 0.2 * Math.sin(phase))
    };

    context.save();
    context.shadowColor = "rgba(130, 240, 207, .72)";
    context.shadowBlur = 15;
    context.fillStyle = palette.paper;
    context.beginPath();
    context.arc(point.x, point.y, 6.8, 0, Math.PI * 2);
    context.fill();
    context.shadowBlur = 0;
    context.fillStyle = palette.mint;
    context.beginPath();
    context.arc(point.x, point.y, 4.2, 0, Math.PI * 2);
    context.fill();

    context.shadowColor = "rgba(130, 240, 207, .42)";
    context.shadowBlur = 12;
    drawArrow(point, tip, palette.mint, 4.2);
    context.shadowBlur = 0;

    context.font = `800 ${geometry.labelSmall}px ${getComputedStyle(document.body).fontFamily}`;
    context.fillStyle = palette.mint;
    context.textAlign = "center";
    context.textBaseline = "bottom";
    const labelY = Math.max(geometry.top + 115, tip.y - 12);
    context.fillText("MOVING FRAME", tip.x, labelY);
    context.restore();
  }

  function drawLabels(geometry) {
    context.save();
    const labelY = geometry.top - 25;
    const quarter = geometry.left + (geometry.right - geometry.left) * .23;
    const threeQuarter = geometry.left + (geometry.right - geometry.left) * .77;
    const family = getComputedStyle(document.body).fontFamily;

    context.font = `700 ${geometry.labelLarge}px ${family}`;
    context.textAlign = "center";
    context.textBaseline = "middle";
    context.fillStyle = palette.cyan;
    context.fillText("U₀  ·  z CHART", quarter, labelY);
    context.fillStyle = palette.violet;
    context.fillText("U∞  ·  w CHART", threeQuarter, labelY);

    context.font = `700 ${geometry.labelSmall}px ${family}`;
    context.fillStyle = "rgba(140, 164, 155, .78)";
    context.textAlign = "right";
    context.fillText("CP¹ BASE", geometry.right, geometry.baseY + 28);

    if (state.showSections) {
      context.fillStyle = "rgba(130, 240, 207, .83)";
      context.textAlign = "left";
      context.fillText("DISTINGUISHED SECTIONS", geometry.left + 6, geometry.baseY - geometry.fiberHeight * .77);
    }
    context.restore();
  }

  function render(position) {
    if (!state.width || !state.height) return;

    const width = state.width;
    const height = state.height;
    const compact = width < 570;
    const geometry = {
      width,
      height,
      left: width * (compact ? .075 : .085),
      right: width * (compact ? .925 : .915),
      top: height * (compact ? .19 : .18),
      bottom: height * .81,
      baseY: height * .7,
      baseWave: Math.max(5, Math.min(10, width * .012)),
      fiberHeight: Math.min(width * (compact ? .25 : .16), height * .34),
      seamWidth: width * (compact ? .16 : .105),
      labelLarge: compact ? 9 : 11,
      labelSmall: compact ? 7 : 8
    };

    context.clearRect(0, 0, width, height);
    drawChartRegions(geometry);
    drawBase(geometry);
    drawRuledSurface(geometry);
    drawGluingWindow(geometry);
    drawMovingFiber(geometry, position);
    drawLabels(geometry);
    updateReadouts(position);
  }

  function requestTick() {
    if (!state.isPlaying || state.animationFrame) return;
    state.animationFrame = requestAnimationFrame(tick);
  }

  function tick(now) {
    state.animationFrame = 0;
    render(currentPosition(now));
    requestTick();
  }

  degreeButtons.forEach((button, index) => {
    button.addEventListener("click", () => {
      state.degree = Number(button.dataset.degree);
      updateDegreeUI();
      render(currentPosition());
    });

    button.addEventListener("keydown", (event) => {
      if (!["ArrowLeft", "ArrowRight", "Home", "End"].includes(event.key)) return;
      event.preventDefault();
      let nextIndex = index;
      if (event.key === "ArrowLeft") nextIndex = Math.max(0, index - 1);
      if (event.key === "ArrowRight") nextIndex = Math.min(degreeButtons.length - 1, index + 1);
      if (event.key === "Home") nextIndex = 0;
      if (event.key === "End") nextIndex = degreeButtons.length - 1;
      degreeButtons[nextIndex].focus();
      degreeButtons[nextIndex].click();
    });
  });

  playToggle.addEventListener("click", () => setPaused(state.isPlaying));

  positionRange.addEventListener("input", () => {
    state.manualPosition = Number(positionRange.value);
    render(state.manualPosition);
  });

  speedRange.addEventListener("input", () => {
    const now = performance.now();
    if (state.isPlaying) {
      state.anchorPosition = currentPosition(now);
      state.anchorTime = now;
    }
    state.speed = Number(speedRange.value);
    speedOutput.textContent = `${state.speed.toFixed(2)}×`;
  });

  sectionsToggle.addEventListener("change", () => {
    state.showSections = sectionsToggle.checked;
    render(currentPosition());
  });

  const handleReducedMotion = (event) => {
    if (event.matches && state.isPlaying) setPaused(true);
  };
  if (typeof reducedMotion.addEventListener === "function") {
    reducedMotion.addEventListener("change", handleReducedMotion);
  }

  const resizeObserver = new ResizeObserver(resizeCanvas);
  resizeObserver.observe(canvas);
  window.addEventListener("resize", resizeCanvas, { passive: true });

  updateDegreeUI();
  updateMotionUI();
  resizeCanvas();
  requestTick();
})();
