const translations = {
  zh: {
    navResearch:"学术研究",navPubs:"论文",navContact:"联系",
    heroKicker:"华东师范大学 · 数学科学学院教授",heroLine1:"结构、动力，",heroLine2:"与智能发现。",
    heroIntro:"我研究代数几何与动力系统，并探索人工智能如何辅助数学推理、拓展战略世界与交互体验。",exploreResearch:"探索研究",playGame:"试玩《无尽》",
    coreFields:"2023 年以来的近期论文",phdYear:"新加坡国立大学数学博士",openQuestions:"开放问题，严谨方法",newFrontiers:"数学与游戏的新边界",
    researchTitle:"近期论文与预印本。",researchLead:"学术研究区只呈现论文本身，并将最新 arXiv 记录置于最前。",viewArxiv:"在 arXiv 查看作者检索结果",
    agTitle:"代数几何",agText:"射影簇、典范除子、环面结构与几何分类。",bgTitle:"双有理几何",bgText:"极小模型纲领、有理连通簇与结构分解。",dsTitle:"动力系统",dsText:"满射自同态、算术度、稠密轨道与动力刚性。",
    currentProgram:"当前研究计划",programText:"满射自同态的分类及其在算术动力系统中的应用，包括 Kawaguchi–Silverman 猜想与 Zariski 稠密轨道猜想。",
    exploratory:"探索方向",aiMathTitle:"让 AI 成为数学探索的伙伴。",aiMathLead:"研究机器智能如何辅助而非替代形式推理、猜想生成、文献导航与数学交流。",
    formalReasoning:"形式推理",formalText:"证明辅助、验证闭环与可解释的数学论证链。",conjectureDiscovery:"猜想发现",conjectureText:"通过计算实验发现值得证明的模式与值得理解的反例。",knowledgeSystems:"数学知识系统",knowledgeText:"结构化连接定义、定理、例子与依赖图谱。",
    creativeLab:"创意实验室",aiGamesTitle:"把游戏变成策略与智能的实验室。",aiGamesLead:"可玩系统让抽象规则变得可见。AI4Games 探索战略智能体、程序化世界，以及把数学结构转化为交互的游戏机制。",
    gameTitle:"疆域争锋",gameText:"从零构建的即时领地策略游戏：连通路径、多建筑指挥、进化式箭塔能力、自适应电脑军团与八张战役地图。",gameFeature1:"拖拽指挥与框选",gameFeature2:"五类建筑自由改建",gameFeature3:"本地账号与持久化战役进度",launchGame:"进入游戏",
    endlessTitle:"无尽",endlessText:"一款完全零付费的无尽防线游戏：塑造可靠牌池、发现跨元素循环，并用主动集火抵御持续增强的外星潮。",endlessFeature1:"六种决定流派的卡牌组合",endlessFeature2:"加权选牌与每波一次免费刷新",endlessFeature3:"主动集火与极限火力时机",launchEndless:"进入《无尽》",
    agentText:"在局部控制、资源压力与网络变化中的决策。",proceduralText:"生成有意义差异的规则，而非装饰性的随机。",learningText:"通过交互理解网络、动力系统与优化。",
    publicationsTitle:"代表论文。",publicationsLead:"涵盖极化自同态、算术动力系统、双有理几何与紧复空间。",downloadCV:"下载简历",allPublications:"查看完整论文列表",
    journeyTitle:"学术经历。",ecnuRole:"数学科学学院教授 / 青年研究员",kiasRole:"研究员",mpiRole:"博士后研究员",nusRole:"数学博士 · 导师：张德祺",
    contactTitle:"一起探索一个困难问题。",contactLead:"欢迎就数学研究、学生培养以及数学、AI 与游戏的跨学科想法交流。",office:"办公室",institution:"单位",address:"地址",footerText:"数学 · 人工智能 · 游戏"
  }
};
const defaultText = new Map();
document.querySelectorAll("[data-i18n]").forEach((node)=>defaultText.set(node.dataset.i18n,node.textContent));
let language = "en";
const languageButton = document.querySelector("#languageButton");
languageButton.addEventListener("click",()=>{
  language = language === "en" ? "zh" : "en";
  document.documentElement.lang = language === "zh" ? "zh-CN" : "en";
  document.querySelectorAll("[data-i18n]").forEach((node)=>{
    node.textContent = language === "zh" ? translations.zh[node.dataset.i18n] || defaultText.get(node.dataset.i18n) : defaultText.get(node.dataset.i18n);
  });
  languageButton.textContent = language === "zh" ? "EN" : "中文";
});
const menuButton = document.querySelector("#menuButton");
const nav = document.querySelector("#mainNav");
menuButton.addEventListener("click",()=>{
  const open = nav.classList.toggle("open");
  menuButton.setAttribute("aria-expanded",String(open));
});
nav.querySelectorAll("a").forEach((link)=>link.addEventListener("click",()=>{nav.classList.remove("open");menuButton.setAttribute("aria-expanded","false");}));
const revealObserver = new IntersectionObserver((entries)=>entries.forEach((entry)=>{if(entry.isIntersecting){entry.target.classList.add("visible");revealObserver.unobserve(entry.target);}}),{threshold:.12});
document.querySelectorAll(".reveal").forEach((node)=>revealObserver.observe(node));
const sections = [...document.querySelectorAll("main section[id]")];
const navLinks = [...nav.querySelectorAll("a[href^='#']")];
const sectionObserver = new IntersectionObserver((entries)=>entries.forEach((entry)=>{if(entry.isIntersecting){navLinks.forEach((link)=>link.classList.toggle("active",link.getAttribute("href") === `#${entry.target.id}`));}}),{rootMargin:"-35% 0px -58%",threshold:0});
sections.forEach((section)=>sectionObserver.observe(section));
document.querySelector("#currentYear").textContent = new Date().getFullYear();

(() => {
  const backgroundCanvas = document.querySelector("#algebraicDynamics");
  const parameterCanvas = document.querySelector("#parameterDynamics");
  if (!backgroundCanvas || !parameterCanvas) return;

  const backgroundContext = backgroundCanvas.getContext("2d", { alpha: true });
  const parameterContext = parameterCanvas.getContext("2d", { alpha: true });
  if (!backgroundContext || !parameterContext) return;
  let context = backgroundContext;

  const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)");
  const fullTurn = Math.PI * 2;
  const lemniscateRotation = 0.45;
  const rotationCosine = Math.cos(lemniscateRotation);
  const rotationSine = Math.sin(lemniscateRotation);
  const curveA = (parameter) => ({
    x: 0.28 * (2 * Math.cos(parameter) + Math.cos(2 * parameter)),
    y: 0.28 * (2 * Math.sin(parameter) - Math.sin(2 * parameter))
  });
  const curveB = (parameter) => {
    const localX = 0.78 * Math.cos(parameter);
    const localY = 1.05 * Math.sin(parameter) * Math.cos(parameter);
    return {
      x: localX * rotationCosine - localY * rotationSine,
      y: localX * rotationSine + localY * rotationCosine
    };
  };
  const cross = (first, second) => first.x * second.y - first.y * second.x;
  const clamp = (value, minimum, maximum) => Math.max(minimum, Math.min(maximum, value));
  const circularDistance = (first, second) => {
    const distance = Math.abs(first - second);
    return Math.min(distance, fullTurn - distance);
  };

  function segmentIntersection(firstStart, firstEnd, secondStart, secondEnd) {
    const firstDirection = { x: firstEnd.x - firstStart.x, y: firstEnd.y - firstStart.y };
    const secondDirection = { x: secondEnd.x - secondStart.x, y: secondEnd.y - secondStart.y };
    const denominator = cross(firstDirection, secondDirection);
    if (Math.abs(denominator) < 1e-9) return null;

    const betweenStarts = { x: secondStart.x - firstStart.x, y: secondStart.y - firstStart.y };
    const firstFraction = cross(betweenStarts, secondDirection) / denominator;
    const secondFraction = cross(betweenStarts, firstDirection) / denominator;
    if (firstFraction < 0 || firstFraction > 1 || secondFraction < 0 || secondFraction > 1) return null;
    return { firstFraction, secondFraction };
  }

  function findIntersections(sampleCount = 360) {
    const firstSamples = [];
    const secondSamples = [];
    for (let index = 0; index <= sampleCount; index += 1) {
      const parameter = (fullTurn * index) / sampleCount;
      firstSamples.push({ parameter, point: curveA(parameter) });
      secondSamples.push({ parameter, point: curveB(parameter) });
    }

    const records = [];
    for (let firstIndex = 0; firstIndex < sampleCount; firstIndex += 1) {
      const firstStart = firstSamples[firstIndex];
      const firstEnd = firstSamples[firstIndex + 1];
      for (let secondIndex = 0; secondIndex < sampleCount; secondIndex += 1) {
        const secondStart = secondSamples[secondIndex];
        const secondEnd = secondSamples[secondIndex + 1];
        const hit = segmentIntersection(firstStart.point, firstEnd.point, secondStart.point, secondEnd.point);
        if (!hit) continue;

        const s = firstStart.parameter + (firstEnd.parameter - firstStart.parameter) * hit.firstFraction;
        const t = secondStart.parameter + (secondEnd.parameter - secondStart.parameter) * hit.secondFraction;
        if (records.some((record) => circularDistance(record.s, s) < 0.02 && circularDistance(record.t, t) < 0.02)) continue;
        const firstPoint = curveA(s);
        const secondPoint = curveB(t);
        records.push({
          s,
          t,
          x: (firstPoint.x + secondPoint.x) / 2,
          y: (firstPoint.y + secondPoint.y) / 2
        });
      }
    }
    return records.sort((first, second) => first.s - second.s || first.t - second.t);
  }

  const intersections = findIntersections();
  [backgroundCanvas, parameterCanvas].forEach((target) => {
    target.dataset.baseIntersections = String(intersections.length);
  });

  let width = 1;
  let height = 1;
  let backgroundWidth = 1;
  let backgroundHeight = 1;
  let parameterWidth = 1;
  let parameterHeight = 1;
  let active = true;
  let inViewport = true;
  let animationFrame = 0;
  let previousFrame = 0;
  let elapsed = 0;

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
    const parameterSize = fitCanvas(parameterCanvas, parameterContext);
    backgroundWidth = backgroundSize.width;
    backgroundHeight = backgroundSize.height;
    parameterWidth = parameterSize.width;
    parameterHeight = parameterSize.height;
    render(elapsed);
  }

  function pointInFrame(point, frame) {
    return {
      x: frame.left + ((point.x + 1) / 2) * frame.size,
      y: frame.top + (1 - (point.y + 1) / 2) * frame.size
    };
  }

  function parameterInFrame(s, t, frame, sLimit, tLimit) {
    return {
      x: frame.left + (s / sLimit) * frame.size,
      y: frame.top + (1 - t / tLimit) * frame.size
    };
  }

  const parameterPointKey = (s, t) => `${Math.round(s * 1000)}:${Math.round(t * 1000)}`;
  let latticeCache = { bucket: -1, points: [], chains: [] };

  function currentParameterLimits(time) {
    const safeTime = Math.max(0, time);
    return {
      s: fullTurn * (3 + 0.76 * Math.log1p(safeTime / 12)),
      t: fullTurn * (3 + 0.68 * Math.log1p(safeTime / 14))
    };
  }

  function buildPeriodicLattice(sLimit, tLimit) {
    const points = [];
    intersections.forEach((intersection, baseIndex) => {
      for (let s = intersection.s, sTurn = 0; s <= sLimit + 1e-7; s += fullTurn, sTurn += 1) {
        for (let t = intersection.t, tTurn = 0; t <= tLimit + 1e-7; t += fullTurn, tTurn += 1) {
          points.push({ s, t, baseIndex, sTurn, tTurn });
        }
      }
    });
    return points.sort((first, second) => first.s - second.s || first.t - second.t);
  }

  function buildArithmeticChains(points, sLimit, tLimit) {
    const lookup = new Map(points.map((point) => [parameterPointKey(point.s, point.t), point]));
    const lines = new Map();
    const epsilon = 1e-6;

    for (let firstIndex = 0; firstIndex < points.length; firstIndex += 1) {
      const first = points[firstIndex];
      for (let secondIndex = firstIndex + 1; secondIndex < points.length; secondIndex += 1) {
        const second = points[secondIndex];
        if (second.s <= first.s + epsilon || second.t <= first.t + epsilon) continue;
        const deltaS = second.s - first.s;
        const deltaT = second.t - first.t;
        if (lookup.has(parameterPointKey(first.s - deltaS, first.t - deltaT))) continue;

        const sequence = [first];
        let current = first;
        let exitsCurrentScale = false;
        while (sequence.length <= 128) {
          const nextS = current.s + deltaS;
          const nextT = current.t + deltaT;
          if (nextS > sLimit + epsilon || nextT > tLimit + epsilon) {
            exitsCurrentScale = true;
            break;
          }
          const next = lookup.get(parameterPointKey(nextS, nextT));
          if (!next) break;
          sequence.push(next);
          current = next;
        }
        if (!exitsCurrentScale || sequence.length < 3) continue;

        const stepLength = Math.hypot(deltaS, deltaT);
        const unitS = deltaS / stepLength;
        const unitT = deltaT / stepLength;
        const intercept = -unitT * first.s + unitS * first.t;
        const lineKey = `${Math.round(unitS * 1000)}:${Math.round(unitT * 1000)}:${Math.round(intercept * 1000)}`;
        const existing = lines.get(lineKey);
        if (!existing || sequence.length > existing.points.length || (sequence.length === existing.points.length && stepLength < existing.stepLength)) {
          lines.set(lineKey, { points: sequence, deltaS, deltaT, stepLength });
        }
      }
    }
    return [...lines.values()].sort((first, second) => second.points.length - first.points.length || first.stepLength - second.stepLength);
  }

  function latticeAt(time, limits) {
    const bucket = Math.floor(time * 2);
    if (bucket !== latticeCache.bucket) {
      const points = buildPeriodicLattice(limits.s, limits.t);
      latticeCache = {
        bucket,
        points,
        chains: buildArithmeticChains(points, limits.s, limits.t)
      };
    }
    return latticeCache;
  }

  function formatPiScale(value) {
    const multiple = value / Math.PI;
    return `${multiple >= 10 ? multiple.toFixed(0) : multiple.toFixed(1)}π`;
  }

  function drawCompleteCurve(curve, frame, colour) {
    context.save();
    context.strokeStyle = colour;
    context.lineWidth = 0.8;
    context.beginPath();
    for (let index = 0; index <= 240; index += 1) {
      const point = pointInFrame(curve((fullTurn * index) / 240), frame);
      if (index === 0) context.moveTo(point.x, point.y);
      else context.lineTo(point.x, point.y);
    }
    context.stroke();
    context.restore();
  }

  function drawTrail(curve, parameterAtTime, time, frame, colour) {
    const segments = width < 400 ? 54 : 72;
    const step = 0.035;
    context.save();
    context.globalCompositeOperation = "lighter";
    for (let index = 1; index <= segments; index += 1) {
      const older = pointInFrame(curve(parameterAtTime(time - index * step)), frame);
      const newer = pointInFrame(curve(parameterAtTime(time - (index - 1) * step)), frame);
      const life = 1 - index / segments;
      context.strokeStyle = colour.replace("ALPHA", String(0.035 + 0.58 * life * life));
      context.lineWidth = 0.55 + life * 1.15;
      context.beginPath();
      context.moveTo(older.x, older.y);
      context.lineTo(newer.x, newer.y);
      context.stroke();
    }
    context.restore();
  }

  function drawParticle(point, colour, coreColour) {
    context.save();
    context.globalCompositeOperation = "lighter";
    const halo = context.createRadialGradient(point.x, point.y, 0, point.x, point.y, 15);
    halo.addColorStop(0, colour.replace("ALPHA", "0.46"));
    halo.addColorStop(0.24, colour.replace("ALPHA", "0.17"));
    halo.addColorStop(1, colour.replace("ALPHA", "0"));
    context.fillStyle = halo;
    context.beginPath();
    context.arc(point.x, point.y, 15, 0, Math.PI * 2);
    context.fill();
    context.fillStyle = coreColour;
    context.beginPath();
    context.arc(point.x, point.y, 2.25, 0, Math.PI * 2);
    context.fill();
    context.restore();
  }

  function drawIntersectionLocus(frame, visibleCount, time) {
    context.save();
    intersections.forEach((record, index) => {
      const point = pointInFrame(record, frame);
      const visible = index < visibleCount;
      const age = time - index * 1.05;
      const pulse = visible && age < 1 ? 4.5 * (1 - Math.max(age, 0)) : 0;
      context.strokeStyle = visible ? "rgba(232, 242, 237, 0.32)" : "rgba(130, 240, 207, 0.055)";
      context.lineWidth = visible ? 1 : 0.7;
      context.beginPath();
      context.arc(point.x, point.y, (visible ? 2.6 : 1.4) + pulse, 0, Math.PI * 2);
      context.stroke();
    });
    context.restore();
  }

  function drawParameterPlane(frame, lattice, limits) {
    const divisions = 4;
    context.save();
    context.lineWidth = 0.7;
    context.font = "5.5px ui-monospace, SFMono-Regular, Consolas, monospace";
    context.textAlign = "center";
    for (let index = 0; index <= divisions; index += 1) {
      const offset = (frame.size * index) / divisions;
      context.strokeStyle = index === 0 || index === divisions
        ? "rgba(130, 240, 207, 0.14)"
        : "rgba(130, 240, 207, 0.065)";
      context.beginPath();
      context.moveTo(frame.left + offset, frame.top);
      context.lineTo(frame.left + offset, frame.top + frame.size);
      context.moveTo(frame.left, frame.top + offset);
      context.lineTo(frame.left + frame.size, frame.top + offset);
      context.stroke();
      context.fillStyle = "rgba(180, 207, 197, 0.4)";
      context.fillText(formatPiScale((limits.s * index) / divisions), frame.left + offset, frame.top + frame.size + 10);
      if (index > 0) {
        context.textAlign = "right";
        context.fillText(formatPiScale((limits.t * (divisions - index)) / divisions), frame.left - 5, frame.top + offset + 2);
        context.textAlign = "center";
      }
    }

    lattice.chains.forEach((chain) => {
      const startRecord = chain.points[0];
      const endRecord = chain.points[chain.points.length - 1];
      const start = parameterInFrame(startRecord.s, startRecord.t, frame, limits.s, limits.t);
      const end = parameterInFrame(endRecord.s, endRecord.t, frame, limits.s, limits.t);
      const strength = Math.min(0.26, 0.08 + chain.points.length * 0.025);
      context.strokeStyle = `rgba(130, 240, 207, ${strength})`;
      context.lineWidth = chain.points.length >= 5 ? 1 : 0.7;
      context.beginPath();
      context.moveTo(start.x, start.y);
      context.lineTo(end.x, end.y);
      context.stroke();
    });

    const pointRadius = lattice.points.length > 220 ? 0.75 : lattice.points.length > 120 ? 0.95 : 1.25;
    lattice.points.forEach((record) => {
      const point = parameterInFrame(record.s, record.t, frame, limits.s, limits.t);
      context.fillStyle = record.baseIndex % 2 === 0
        ? "rgba(232, 242, 237, 0.82)"
        : "rgba(130, 240, 207, 0.72)";
      context.beginPath();
      context.arc(point.x, point.y, pointRadius, 0, Math.PI * 2);
      context.fill();
    });

    context.strokeStyle = "rgba(231, 185, 92, 0.34)";
    context.lineWidth = 1;
    context.beginPath();
    context.moveTo(frame.left + frame.size, frame.top);
    context.lineTo(frame.left + frame.size, frame.top + frame.size);
    context.moveTo(frame.left, frame.top);
    context.lineTo(frame.left + frame.size, frame.top);
    context.stroke();
    context.restore();
  }

  function drawLabel(text, x, y, colour = "rgba(202, 222, 214, 0.62)", size = 8) {
    context.save();
    context.fillStyle = colour;
    context.font = `${size}px ui-monospace, SFMono-Regular, Consolas, monospace`;
    context.fillText(text, x, y);
    context.restore();
  }

  function render(time) {
    const sNow = (time * 0.56) % fullTurn;
    const tNow = (time * 0.43 + 1.35) % fullTurn;
    const parameterLimits = currentParameterLimits(time);
    const lattice = latticeAt(time, parameterLimits);
    const visibleCount = reducedMotion.matches
      ? intersections.length
      : Math.min(intersections.length, Math.max(0, Math.floor(time / 1.05) + 1));
    parameterCanvas.dataset.points = String(lattice.points.length);
    parameterCanvas.dataset.arithmeticChains = String(lattice.chains.length);
    parameterCanvas.dataset.maxChainLength = String(lattice.chains[0]?.points.length || 0);
    parameterCanvas.dataset.sScale = parameterLimits.s.toFixed(3);
    parameterCanvas.dataset.tScale = parameterLimits.t.toFixed(3);

    context = backgroundContext;
    width = backgroundWidth;
    height = backgroundHeight;
    context.clearRect(0, 0, width, height);
    const narrow = width < 700;
    const plotSize = Math.max(
      340,
      Math.min(width * (narrow ? 1.55 : 1.03), height * (narrow ? 0.76 : 1.22))
    );
    const plotCentreX = width * (narrow ? 0.56 : 0.62);
    const plotCentreY = height * (narrow ? 0.54 : 0.52);
    const plotFrame = {
      left: plotCentreX - plotSize / 2,
      top: plotCentreY - plotSize / 2,
      size: plotSize
    };
    drawCompleteCurve(curveA, plotFrame, "rgba(83, 207, 219, 0.17)");
    drawCompleteCurve(curveB, plotFrame, "rgba(231, 185, 92, 0.15)");
    drawIntersectionLocus(plotFrame, visibleCount, time);
    drawTrail(curveA, (trailTime) => trailTime * 0.56, time, plotFrame, "rgba(83, 207, 219, ALPHA)");
    drawTrail(curveB, (trailTime) => trailTime * 0.43 + 1.35, time, plotFrame, "rgba(231, 185, 92, ALPHA)");
    drawParticle(pointInFrame(curveA(sNow), plotFrame), "rgba(83, 207, 219, ALPHA)", "rgba(226, 255, 249, 0.98)");
    drawParticle(pointInFrame(curveB(tNow), plotFrame), "rgba(231, 185, 92, ALPHA)", "rgba(255, 244, 215, 0.98)");

    if (!narrow) {
      drawLabel("a(s) · DELTOID", clamp(plotFrame.left + 34, 28, width - 190), height - 42, "rgba(83, 207, 219, 0.36)", 7);
      drawLabel("b(t) · GERONO LEMNISCATE", clamp(plotFrame.left + 154, 148, width - 210), height - 42, "rgba(231, 185, 92, 0.34)", 7);
    }

    context = parameterContext;
    width = parameterWidth;
    height = parameterHeight;
    context.clearRect(0, 0, width, height);
    const parameterSize = Math.max(150, Math.min(width - 68, height - 132));
    const parameterFrame = {
      left: (width - parameterSize) / 2,
      top: 80 + Math.max(0, (height - 132 - parameterSize) / 2),
      size: parameterSize
    };
    drawLabel("EXPANDING PARAMETER LATTICE", 30, 27, "rgba(231, 185, 92, 0.76)", 7);
    drawLabel("p < q ⇔ s(p) < s(q) AND t(p) < t(q)", 30, 43, "rgba(202, 222, 214, 0.58)", 6.4);
    drawLabel(`a(s) = b(t) · ${lattice.points.length} POINTS · ${lattice.chains.length} CHAINS`, 30, 58, "rgba(130, 240, 207, 0.62)", 6.2);
    drawParameterPlane(parameterFrame, lattice, parameterLimits);
    drawLabel("s", parameterFrame.left + parameterFrame.size + 4, parameterFrame.top + parameterFrame.size / 2 + 3, undefined, 7);
    drawLabel("t", parameterFrame.left + parameterFrame.size / 2 + 4, parameterFrame.top - 4, undefined, 7);
    drawLabel(`S ≤ ${formatPiScale(parameterLimits.s)} · T ≤ ${formatPiScale(parameterLimits.t)}`, parameterFrame.left, height - 25, "rgba(231, 185, 92, 0.52)", 6.2);
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
  resizeObserver.observe(parameterCanvas);
  const visibilityObserver = new IntersectionObserver(([entry]) => {
    inViewport = entry.isIntersecting;
    setActive(inViewport);
  }, { threshold: 0.02 });
  visibilityObserver.observe(backgroundCanvas);
  document.addEventListener("visibilitychange", () => setActive(inViewport));
  reducedMotion.addEventListener("change", () => setActive(inViewport));
  resizeCanvases();
  setActive(true);
})();
