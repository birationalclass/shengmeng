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

  function drawSurfacePreview(timestamp = 0) {
    const canvas = document.querySelector("#surfacePreview");
    if (!canvas) return;
    const bounds = canvas.getBoundingClientRect();
    const ratio = Math.min(window.devicePixelRatio || 1, 1.6);
    const nextWidth = Math.max(1, Math.round(bounds.width * ratio));
    const nextHeight = Math.max(1, Math.round(bounds.height * ratio));
    if (canvas.width !== nextWidth || canvas.height !== nextHeight) {
      canvas.width = nextWidth;
      canvas.height = nextHeight;
    }
    const context = canvas.getContext("2d");
    const width = canvas.width;
    const height = canvas.height;
    context.clearRect(0, 0, width, height);
    context.fillStyle = palette.ink;
    context.fillRect(0, 0, width, height);

    const cycle = (timestamp % 9000) / 9000;
    const morph = .5 - .5 * Math.cos(cycle * Math.PI * 2);
    const power = 10 - 8 * morph;
    const yaw = -.62 + timestamp * .000045;
    const pitch = -.36;
    const scale = Math.min(width, height) * .28;
    const centerX = width * .48;
    const centerY = height * .51;

    function signedPower(value, exponent) {
      return Math.sign(value) * Math.pow(Math.abs(value), exponent);
    }

    function project(longitude, latitude) {
      const exponent = 2 / power;
      const latitudeCosine = signedPower(Math.cos(latitude), exponent);
      let x = latitudeCosine * signedPower(Math.cos(longitude), exponent);
      let y = signedPower(Math.sin(latitude), exponent);
      let z = latitudeCosine * signedPower(Math.sin(longitude), exponent);
      const rotatedX = x * Math.cos(yaw) + z * Math.sin(yaw);
      const rotatedZ = -x * Math.sin(yaw) + z * Math.cos(yaw);
      const rotatedY = y * Math.cos(pitch) - rotatedZ * Math.sin(pitch);
      const depth = y * Math.sin(pitch) + rotatedZ * Math.cos(pitch);
      const perspective = 1 / (1.18 - depth * .16);
      return [centerX + rotatedX * scale * perspective, centerY - rotatedY * scale * perspective, depth];
    }

    const curves = [];
    for (let latitudeIndex = -5; latitudeIndex <= 5; latitudeIndex += 1) {
      const latitude = latitudeIndex * Math.PI / 12;
      curves.push(Array.from({ length: 97 }, (_, index) => project(index / 96 * Math.PI * 2, latitude)));
    }
    for (let longitudeIndex = 0; longitudeIndex < 16; longitudeIndex += 1) {
      const longitude = longitudeIndex / 16 * Math.PI * 2;
      curves.push(Array.from({ length: 65 }, (_, index) => project(longitude, -Math.PI / 2 + index / 64 * Math.PI)));
    }
    curves.sort((first, second) => {
      const mean = (curve) => curve.reduce((sum, point) => sum + point[2], 0) / curve.length;
      return mean(first) - mean(second);
    });
    context.lineCap = "round";
    context.lineJoin = "round";
    curves.forEach((curve) => {
      const depth = curve.reduce((sum, point) => sum + point[2], 0) / curve.length;
      const alpha = .18 + .55 * ((depth + 1.4) / 2.8);
      context.beginPath();
      curve.forEach((point, index) => {
        if (index === 0) context.moveTo(point[0], point[1]); else context.lineTo(point[0], point[1]);
      });
      context.strokeStyle = `rgba(125,235,201,${Math.max(.12, Math.min(.74, alpha))})`;
      context.lineWidth = ratio * (depth > 0 ? 1.05 : .68);
      context.stroke();
    });

    const glow = context.createRadialGradient(centerX, centerY, 0, centerX, centerY, scale * 1.6);
    glow.addColorStop(0, "rgba(82,202,212,.1)");
    glow.addColorStop(.68, "rgba(82,202,212,.025)");
    glow.addColorStop(1, "rgba(7,21,19,0)");
    context.globalCompositeOperation = "screen";
    context.fillStyle = glow;
    context.fillRect(0, 0, width, height);
    context.globalCompositeOperation = "source-over";
    context.fillStyle = "rgba(221,179,91,.7)";
    context.font = `${Math.max(9, width * .011)}px ui-monospace, monospace`;
    context.fillText(`BGN · m ≈ ${String(Math.round(morph * 320)).padStart(3, "0")}`, width * .055, height * .1);
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

  function drawPascalPreview() {
    const canvas = document.querySelector("#pascalPreview");
    if (!canvas) return;
    const context = fitCanvas(canvas);
    const width = canvas.width;
    const height = canvas.height;
    context.fillStyle = palette.ink;
    context.fillRect(0, 0, width, height);

    const cross = (first, second) => [
      first[1] * second[2] - first[2] * second[1],
      first[2] * second[0] - first[0] * second[2],
      first[0] * second[1] - first[1] * second[0]
    ];
    const angles = [-1.829, -.886, -.042, .261, 1.198, 2.922];
    const points = angles.map((angle) => [1.5 * Math.cos(angle), .84 * Math.sin(angle), 1]);
    const sides = points.map((point, index) => cross(point, points[(index + 1) % points.length]));
    const intersections = [[0, 3], [1, 4], [2, 5]].map(([first, second]) => {
      const point = cross(sides[first], sides[second]);
      return [point[0] / point[2], point[1] / point[2]];
    });
    const pascal = cross([...intersections[0], 1], [...intersections[1], 1]);
    const bounds = { minX: -1.75, maxX: 3.08, minY: -3.35, maxY: 1.72 };
    const scale = Math.min(width * .82 / (bounds.maxX - bounds.minX), height * .78 / (bounds.maxY - bounds.minY));
    const centerX = (bounds.minX + bounds.maxX) / 2;
    const centerY = (bounds.minY + bounds.maxY) / 2;
    const project = ([x, y]) => [width * .5 + (x - centerX) * scale, height * .5 - (y - centerY) * scale];

    context.save();
    context.strokeStyle = "rgba(130,240,207,.32)";
    context.lineWidth = 1.4;
    context.beginPath();
    for (let index = 0; index <= 180; index += 1) {
      const angle = Math.PI * 2 * index / 180;
      const screen = project([1.5 * Math.cos(angle), .84 * Math.sin(angle)]);
      if (index === 0) context.moveTo(screen[0], screen[1]);
      else context.lineTo(screen[0], screen[1]);
    }
    context.closePath();
    context.stroke();

    const pairColours = [palette.gold, palette.cyan, "#a899e9"];
    points.forEach((point, index) => {
      const first = project(point);
      const second = project(points[(index + 1) % points.length]);
      context.strokeStyle = pairColours[index % 3];
      context.globalAlpha = .58;
      context.beginPath();
      context.moveTo(first[0], first[1]);
      context.lineTo(second[0], second[1]);
      context.stroke();
    });

    const lineY = (x) => -(pascal[0] * x + pascal[2]) / pascal[1];
    const lineStart = project([bounds.minX, lineY(bounds.minX)]);
    const lineEnd = project([bounds.maxX, lineY(bounds.maxX)]);
    context.globalAlpha = 1;
    context.strokeStyle = palette.mint;
    context.lineWidth = 1.8;
    context.shadowColor = palette.mint;
    context.shadowBlur = 14;
    context.beginPath();
    context.moveTo(lineStart[0], lineStart[1]);
    context.lineTo(lineEnd[0], lineEnd[1]);
    context.stroke();
    context.shadowBlur = 0;

    points.forEach((point, index) => {
      const screen = project(point);
      context.fillStyle = palette.paper;
      context.beginPath();
      context.arc(screen[0], screen[1], 3, 0, Math.PI * 2);
      context.fill();
      context.fillStyle = "rgba(232,242,237,.72)";
      context.font = `${Math.max(9, width * .012)}px Georgia, serif`;
      context.fillText("ABCDEF"[index], screen[0] + 7, screen[1] - 6);
    });
    intersections.forEach((point, index) => {
      const screen = project(point);
      context.fillStyle = pairColours[index];
      context.beginPath();
      context.arc(screen[0], screen[1], 3.6, 0, Math.PI * 2);
      context.fill();
      context.fillStyle = pairColours[index];
      context.font = `${Math.max(9, width * .012)}px ui-monospace, monospace`;
      context.fillText("XYZ"[index], screen[0] + 7, screen[1] - 6);
    });
    context.restore();
  }

  function drawAll() {
    drawSurfacePreview(performance.now());
    drawJuliaPreview();
    drawChaosPreview();
    drawBundlePreview();
    drawPascalPreview();
  }

  let resizeTimer = 0;
  window.addEventListener("resize", () => {
    window.clearTimeout(resizeTimer);
    resizeTimer = window.setTimeout(drawAll, 140);
  });

  const year = document.querySelector("#currentYear");
  if (year) year.textContent = String(new Date().getFullYear());
  drawAll();

  if (!window.matchMedia("(prefers-reduced-motion: reduce)").matches) {
    const animateSurface = (timestamp) => {
      drawSurfacePreview(timestamp);
      window.requestAnimationFrame(animateSurface);
    };
    window.requestAnimationFrame(animateSurface);
  }
})();
