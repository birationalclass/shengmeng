const svgNS = "http://www.w3.org/2000/svg";

const clamp = (value, min, max) => Math.max(min, Math.min(max, value));
const makeSvg = (tag, attributes = {}) => {
  const node = document.createElementNS(svgNS, tag);
  Object.entries(attributes).forEach(([key, value]) => node.setAttribute(key, String(value)));
  return node;
};

document.querySelector("#currentYear").textContent = new Date().getFullYear();

const menuButton = document.querySelector("#menuButton");
const nav = document.querySelector("#studyNav");
menuButton.addEventListener("click", () => {
  const open = nav.classList.toggle("open");
  menuButton.setAttribute("aria-expanded", String(open));
});
nav.querySelectorAll("a").forEach((link) => link.addEventListener("click", () => {
  nav.classList.remove("open");
  menuButton.setAttribute("aria-expanded", "false");
}));

const revealObserver = new IntersectionObserver((entries) => {
  entries.forEach((entry) => {
    if (!entry.isIntersecting) return;
    entry.target.classList.add("visible");
    revealObserver.unobserve(entry.target);
  });
}, { threshold: 0.1 });
document.querySelectorAll(".reveal").forEach((node) => revealObserver.observe(node));

const sections = [...document.querySelectorAll("main section[id], article[id]")];
const navLinks = [...nav.querySelectorAll("a[href^='#']")];
const sectionObserver = new IntersectionObserver((entries) => {
  entries.forEach((entry) => {
    if (!entry.isIntersecting) return;
    navLinks.forEach((link) => link.classList.toggle("active", link.getAttribute("href") === `#${entry.target.id}`));
  });
}, { rootMargin: "-35% 0px -58%", threshold: 0 });
sections.forEach((section) => sectionObserver.observe(section));

const fieldNames = {
  topology: "代数拓扑",
  geometry: "代数几何",
  dynamics: "动力系统",
  ai4math: "AI4Math"
};
const fieldCards = [...document.querySelectorAll(".field-card")];
const noteCards = [...document.querySelectorAll(".note-card")];
const emptyState = document.querySelector("#emptyState");
const filterStatus = document.querySelector("#filterStatus");
fieldCards.forEach((card) => card.addEventListener("click", () => {
  const field = card.dataset.filter;
  fieldCards.forEach((item) => {
    const active = item === card;
    item.classList.toggle("active", active);
    item.setAttribute("aria-pressed", String(active));
  });
  let count = 0;
  noteCards.forEach((note) => {
    const visible = note.dataset.field === field;
    note.hidden = !visible;
    if (visible) count += 1;
  });
  emptyState.hidden = count > 0;
  filterStatus.textContent = `当前显示：${fieldNames[field]} · ${count} 篇`;
  document.querySelector("#notes").scrollIntoView({ behavior: "smooth", block: "start" });
}));

const makePlayer = (range, button, update) => {
  let frame = 0;
  let start = 0;
  let initial = Number(range.value) / 100;
  const stop = () => {
    cancelAnimationFrame(frame);
    frame = 0;
    button.textContent = "播放收缩";
  };
  const tick = (time) => {
    if (!start) start = time;
    const elapsed = (time - start) / 1800;
    const value = Math.min(1, initial + elapsed);
    range.value = String(Math.round(value * 100));
    update(value);
    if (value < 1) frame = requestAnimationFrame(tick);
    else stop();
  };
  button.addEventListener("click", () => {
    if (frame) return stop();
    if (Number(range.value) >= 100) range.value = "0";
    initial = Number(range.value) / 100;
    start = 0;
    button.textContent = "暂停";
    frame = requestAnimationFrame(tick);
  });
  range.addEventListener("input", () => {
    stop();
    update(Number(range.value) / 100);
  });
  return { stop };
};

const circleRange = document.querySelector("#circleRange");
const circleValue = document.querySelector("#circleValue");
const circlePointsGroup = document.querySelector("#circlePoints");
const circleArrowsGroup = document.querySelector("#circleArrows");
const dragPoint = document.querySelector("#dragPoint");
const dragGuide = document.querySelector("#dragGuide");
const circleDiagram = document.querySelector("#circleDiagram");
const center = { x: 300, y: 175 };
const targetRadius = 95;
const ringMin = 61;
const ringMax = 133;
let draggedBase = { angle: 0, radius: 110 };

const circleSamples = [
  [0.28, 70], [0.88, 121], [1.56, 77], [2.28, 126],
  [3.05, 68], [3.72, 118], [4.46, 81], [5.34, 128]
].map(([angle, radius]) => {
  const line = makeSvg("line");
  const point = makeSvg("circle", { r: 5 });
  circleArrowsGroup.append(line);
  circlePointsGroup.append(point);
  return { angle, radius, line, point };
});

const polarPoint = (angle, radius) => ({
  x: center.x + Math.cos(angle) * radius,
  y: center.y + Math.sin(angle) * radius
});

const updateCircle = (t) => {
  circleValue.textContent = `t = ${t.toFixed(2)}`;
  circleSamples.forEach(({ angle, radius, line, point }) => {
    const startPoint = polarPoint(angle, radius);
    const currentPoint = polarPoint(angle, radius + (targetRadius - radius) * t);
    line.setAttribute("x1", startPoint.x); line.setAttribute("y1", startPoint.y);
    line.setAttribute("x2", currentPoint.x); line.setAttribute("y2", currentPoint.y);
    point.setAttribute("cx", currentPoint.x); point.setAttribute("cy", currentPoint.y);
  });
  const base = polarPoint(draggedBase.angle, draggedBase.radius);
  const current = polarPoint(draggedBase.angle, draggedBase.radius + (targetRadius - draggedBase.radius) * t);
  dragGuide.setAttribute("x2", base.x); dragGuide.setAttribute("y2", base.y);
  dragPoint.setAttribute("cx", current.x); dragPoint.setAttribute("cy", current.y);
};

const pointerToSvg = (event, svg) => {
  const point = svg.createSVGPoint();
  point.x = event.clientX; point.y = event.clientY;
  return point.matrixTransform(svg.getScreenCTM().inverse());
};
let dragging = false;
dragPoint.addEventListener("pointerdown", (event) => {
  dragging = true;
  dragPoint.setPointerCapture(event.pointerId);
  circleRange.value = "0";
  updateCircle(0);
});
dragPoint.addEventListener("pointermove", (event) => {
  if (!dragging) return;
  const point = pointerToSvg(event, circleDiagram);
  const dx = point.x - center.x;
  const dy = point.y - center.y;
  draggedBase = {
    angle: Math.atan2(dy, dx),
    radius: clamp(Math.hypot(dx, dy), ringMin + 4, ringMax - 4)
  };
  updateCircle(0);
});
const endDrag = () => { dragging = false; };
dragPoint.addEventListener("pointerup", endDrag);
dragPoint.addEventListener("pointercancel", endDrag);
dragPoint.addEventListener("keydown", (event) => {
  const delta = event.shiftKey ? 8 : 3;
  if (event.key === "ArrowUp") draggedBase.radius = clamp(draggedBase.radius - delta, ringMin + 4, ringMax - 4);
  else if (event.key === "ArrowDown") draggedBase.radius = clamp(draggedBase.radius + delta, ringMin + 4, ringMax - 4);
  else if (event.key === "ArrowLeft") draggedBase.angle -= 0.08;
  else if (event.key === "ArrowRight") draggedBase.angle += 0.08;
  else return;
  event.preventDefault();
  circleRange.value = "0";
  updateCircle(0);
});
makePlayer(circleRange, document.querySelector("#circlePlay"), updateCircle);
updateCircle(0);

const figureRange = document.querySelector("#figureRange");
const figureValue = document.querySelector("#figureValue");
const figurePath = document.querySelector("#figureTarget");
const figureNeighborhood = document.querySelector("#figureNeighborhood");
const vertexNeighborhood = document.querySelector("#vertexNeighborhood");
const figurePointsGroup = document.querySelector("#figurePoints");
const figureArrowsGroup = document.querySelector("#figureArrows");
const pathLength = figurePath.getTotalLength();
const figureSamples = [0.07, 0.17, 0.29, 0.41, 0.59, 0.71, 0.83, 0.93].map((ratio, index) => {
  const length = pathLength * ratio;
  const point = figurePath.getPointAtLength(length);
  const before = figurePath.getPointAtLength(Math.max(0, length - 1));
  const after = figurePath.getPointAtLength(Math.min(pathLength, length + 1));
  const tangent = { x: after.x - before.x, y: after.y - before.y };
  const magnitude = Math.hypot(tangent.x, tangent.y) || 1;
  const normal = { x: -tangent.y / magnitude, y: tangent.x / magnitude };
  const offset = (index % 2 ? -1 : 1) * (23 + (index % 3) * 4);
  const start = { x: point.x + normal.x * offset, y: point.y + normal.y * offset };
  const line = makeSvg("line", { x1: start.x, y1: start.y });
  const dot = makeSvg("circle", { r: 5 });
  figureArrowsGroup.append(line);
  figurePointsGroup.append(dot);
  return { point, start, line, dot };
});

const updateFigure = (t) => {
  figureValue.textContent = `t = ${t.toFixed(2)}`;
  figureNeighborhood.style.strokeWidth = String(84 - 76 * t);
  figureNeighborhood.style.opacity = String(0.95 - 0.55 * t);
  vertexNeighborhood.setAttribute("r", String(43 - 35 * t));
  vertexNeighborhood.style.opacity = String(1 - 0.62 * t);
  figureSamples.forEach(({ point, start, line, dot }) => {
    const current = {
      x: start.x + (point.x - start.x) * t,
      y: start.y + (point.y - start.y) * t
    };
    line.setAttribute("x2", current.x); line.setAttribute("y2", current.y);
    dot.setAttribute("cx", current.x); dot.setAttribute("cy", current.y);
  });
};
makePlayer(figureRange, document.querySelector("#figurePlay"), updateFigure);
updateFigure(0);
