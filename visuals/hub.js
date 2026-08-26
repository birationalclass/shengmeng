(() => {
  "use strict";

  const palette = {
    ink: "#071513",
    mint: "#82f0cf",
    cyan: "#53cfdb",
    gold: "#e7b95c",
    paper: "#e8f2ed"
  };

  function fitCanvas(canvas) {
    const bounds = canvas.getBoundingClientRect();
    const ratio = Math.min(window.devicePixelRatio || 1, 1.6);
    canvas.width = Math.max(1, Math.round(bounds.width * ratio));
    canvas.height = Math.max(1, Math.round(bounds.height * ratio));
    return canvas.getContext("2d");
  }

  function drawJuliaPreview() {
    const canvas = document.querySelector("#juliaPreview");
    if (!canvas) return;
    const context = fitCanvas(canvas);
    const ratio = canvas.width / canvas.height;
    const width = Math.min(380, canvas.width);
    const height = Math.max(1, Math.round(width / ratio));
    const buffer = document.createElement("canvas");
    buffer.width = width;
    buffer.height = height;
    const bufferContext = buffer.getContext("2d");
    const image = bufferContext.createImageData(width, height);
    const cReal = -0.52;
    const cImaginary = 0.59;

    for (let y = 0; y < height; y += 1) {
      for (let x = 0; x < width; x += 1) {
        let zx = 2.65 * (x - width * .5) / height - .16;
        let zy = 2.65 * (height * .5 - y) / height;
        let minimum = 8;
        let escaped = 0;
        for (let iteration = 0; iteration < 54; iteration += 1) {
          const nextX = zx * zx - zy * zy + cReal;
          zy = 2 * zx * zy + cImaginary;
          zx = nextX;
          const radius = zx * zx + zy * zy;
          minimum = Math.min(minimum, radius);
          if (radius > 48) {
            escaped = iteration / 54;
            break;
          }
        }
        const position = (y * width + x) * 4;
        const edge = Math.max(0, 1 - Math.abs(minimum - .8));
        const glow = Math.min(1, escaped * 2.4 + edge * .55);
        image.data[position] = Math.round(11 + 102 * glow + 120 * edge);
        image.data[position + 1] = Math.round(24 + 190 * glow + 40 * edge);
        image.data[position + 2] = Math.round(22 + 165 * glow + 70 * edge);
        image.data[position + 3] = 255;
      }
    }
    bufferContext.putImageData(image, 0, 0);
    context.imageSmoothingEnabled = true;
    context.drawImage(buffer, 0, 0, canvas.width, canvas.height);

    const gradient = context.createLinearGradient(0, 0, canvas.width, canvas.height);
    gradient.addColorStop(0, "rgba(231,185,92,.12)");
    gradient.addColorStop(.5, "rgba(7,21,19,0)");
    gradient.addColorStop(1, "rgba(83,207,219,.16)");
    context.fillStyle = gradient;
    context.fillRect(0, 0, canvas.width, canvas.height);
  }

  function drawChaosPreview() {
    const canvas = document.querySelector("#chaosPreview");
    if (!canvas) return;
    const context = fitCanvas(canvas);
    context.fillStyle = palette.ink;
    context.fillRect(0, 0, canvas.width, canvas.height);

    const points = [];
    let x = .1;
    let y = 0;
    let z = 0;
    const dt = .006;
    for (let index = 0; index < 7000; index += 1) {
      const dx = 10 * (y - x);
      const dy = x * (28 - z) - y;
      const dz = x * y - (8 / 3) * z;
      x += dx * dt;
      y += dy * dt;
      z += dz * dt;
      if (index > 500 && index % 3 === 0) points.push([x, z]);
    }

    const project = ([px, pz]) => [
      canvas.width * (.5 + px / 48),
      canvas.height * (.88 - pz / 55)
    ];
    context.lineJoin = "round";
    context.lineCap = "round";
    [12, 5, 1.5].forEach((lineWidth, layer) => {
      context.beginPath();
      points.forEach((point, index) => {
        const [sx, sy] = project(point);
        if (index === 0) context.moveTo(sx, sy);
        else context.lineTo(sx, sy);
      });
      context.lineWidth = lineWidth;
      context.strokeStyle = layer === 0 ? "rgba(83,207,219,.06)" : layer === 1 ? "rgba(83,207,219,.15)" : palette.cyan;
      context.stroke();
    });
    const finalPoint = project(points[points.length - 1]);
    context.beginPath();
    context.arc(finalPoint[0], finalPoint[1], 4.5, 0, Math.PI * 2);
    context.fillStyle = palette.paper;
    context.shadowColor = palette.mint;
    context.shadowBlur = 16;
    context.fill();
    context.shadowBlur = 0;
  }

  function drawBundlePreview() {
    const canvas = document.querySelector("#bundlePreview");
    if (!canvas) return;
    const context = fitCanvas(canvas);
    const width = canvas.width;
    const height = canvas.height;
    context.fillStyle = palette.ink;
    context.fillRect(0, 0, width, height);
    context.lineCap = "round";

    const centers = [[width * .29, height * .53], [width * .71, height * .53]];
    centers.forEach(([cx, cy], chart) => {
      const radiusX = width * .18;
      const radiusY = height * .29;
      context.beginPath();
      context.ellipse(cx, cy, radiusX, radiusY, 0, 0, Math.PI * 2);
      context.strokeStyle = chart === 0 ? "rgba(83,207,219,.52)" : "rgba(231,185,92,.55)";
      context.lineWidth = 1.4;
      context.stroke();

      for (let index = 0; index < 12; index += 1) {
        const angle = (Math.PI * 2 * index) / 12;
        const bx = cx + radiusX * Math.cos(angle);
        const by = cy + radiusY * Math.sin(angle);
        const phase = angle * (chart === 0 ? 0 : 2);
        const length = height * .095;
        context.beginPath();
        context.moveTo(bx - Math.cos(phase) * length, by - Math.sin(phase) * length);
        context.lineTo(bx + Math.cos(phase) * length, by + Math.sin(phase) * length);
        context.strokeStyle = chart === 0 ? "rgba(130,240,207,.43)" : "rgba(231,185,92,.45)";
        context.lineWidth = 1;
        context.stroke();
      }
    });

    const bridge = context.createLinearGradient(width * .43, 0, width * .57, 0);
    bridge.addColorStop(0, "rgba(83,207,219,.08)");
    bridge.addColorStop(.5, "rgba(130,240,207,.38)");
    bridge.addColorStop(1, "rgba(231,185,92,.08)");
    context.fillStyle = bridge;
    context.fillRect(width * .43, height * .29, width * .14, height * .48);
    context.fillStyle = "rgba(232,242,237,.74)";
    context.font = `${Math.max(10, width * .017)}px Georgia, serif`;
    context.textAlign = "center";
    context.fillText("w = 1/z", width * .5, height * .2);
    context.fillStyle = "rgba(130,240,207,.7)";
    context.font = `${Math.max(8, width * .012)}px ui-monospace, monospace`;
    context.fillText("U₀  ∩  U∞", width * .5, height * .88);
  }

  function drawAll() {
    drawJuliaPreview();
    drawChaosPreview();
    drawBundlePreview();
  }

  let resizeTimer = 0;
  window.addEventListener("resize", () => {
    window.clearTimeout(resizeTimer);
    resizeTimer = window.setTimeout(drawAll, 140);
  });

  const year = document.querySelector("#currentYear");
  if (year) year.textContent = String(new Date().getFullYear());
  drawAll();
})();
