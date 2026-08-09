(() => {
  "use strict";

  const TAU = Math.PI * 2;
  const FRAME_WIDTH = 512;
  const FRAME_HEIGHT = 288;
  const FRAME_COLUMNS = 5;
  const FRAME_COUNT = 10;
  const LOOP_SECONDS = 3.6;
  const MAX_GAME_BOSS_WIDTH = 360;

  const PALETTES = {
    gold: { name:"电影暖金", hot:"#fff7d2", mid:"#ffc66f", cool:"#9c4cff" },
    blue: { name:"蓝白高温", hot:"#ffffff", mid:"#9aeaff", cool:"#315dff" },
    violet: { name:"紫色电浆", hot:"#fff5ff", mid:"#d49aff", cool:"#6537d8" },
    red: { name:"暗红巨兽", hot:"#fff0d4", mid:"#ff7658", cool:"#7f153e" }
  };

  function rgba(hex, alpha) {
    const value = Number.parseInt(hex.slice(1), 16);
    return `rgba(${(value >> 16) & 255},${(value >> 8) & 255},${value & 255},${alpha})`;
  }

  const sheets = Object.fromEntries(Object.keys(PALETTES).map((name) => {
    const image = new Image();
    const entry = { image, ready:false, failed:false };
    image.decoding = "async";
    image.onload = () => { entry.ready = true; };
    image.onerror = () => { entry.failed = true; };
    image.src = new URL(`assets/black-hole/black-hole-${name}.webp?v=20260809-loop37`, document.baseURI).href;
    if (image.decode) image.decode().then(() => { entry.ready = true; }).catch(() => {});
    return [name, entry];
  }));

  function sheetFor(paletteName) {
    const entry = sheets[paletteName] || sheets.violet;
    if (!entry.ready && entry.image.complete && entry.image.naturalWidth) entry.ready = true;
    return entry;
  }

  function visualSize(radius) {
    const width = Math.min(MAX_GAME_BOSS_WIDTH, Math.max(128, radius * 5.55));
    return { width, height:width * FRAME_HEIGHT / FRAME_WIDTH };
  }

  function drawFrame(ctx, image, index, width, height, alpha = 1) {
    const sourceX = (index % FRAME_COLUMNS) * FRAME_WIDTH;
    const sourceY = Math.floor(index / FRAME_COLUMNS) * FRAME_HEIGHT;
    ctx.globalAlpha = alpha;
    ctx.drawImage(image, sourceX, sourceY, FRAME_WIDTH, FRAME_HEIGHT, -width / 2, -height / 2, width, height);
  }

  function drawFallback(ctx, enemy, radius, elapsed) {
    const palette = PALETTES[enemy.blackHolePalette] || PALETTES.violet;
    const { width, height } = visualSize(radius);
    const core = Math.min(width, height) * .24;
    ctx.save();
    ctx.rotate((enemy.visualRoll || 0) * Math.PI / 720);
    const glow = ctx.createRadialGradient(0, 0, core * .65, 0, 0, width * .48);
    glow.addColorStop(0, "rgba(0,0,0,0)");
    glow.addColorStop(.42, rgba(palette.mid, .16));
    glow.addColorStop(.72, rgba(palette.cool, .08));
    glow.addColorStop(1, rgba(palette.cool, 0));
    ctx.fillStyle = glow;
    ctx.fillRect(-width / 2, -height / 2, width, height);
    ctx.rotate(elapsed * .22);
    ctx.shadowColor = palette.mid;
    ctx.shadowBlur = 20;
    ctx.strokeStyle = rgba(palette.mid, .88);
    ctx.lineWidth = Math.max(8, radius * .17);
    ctx.beginPath();
    ctx.ellipse(0, 0, width * .39, height * .19, 0, 0, TAU);
    ctx.stroke();
    ctx.rotate(-elapsed * .22);
    ctx.fillStyle = "#000";
    ctx.beginPath();
    ctx.arc(0, 0, core, 0, TAU);
    ctx.fill();
    ctx.strokeStyle = rgba(palette.hot, .82);
    ctx.lineWidth = 2;
    ctx.stroke();
    ctx.restore();
  }

  function draw(ctx, enemy, radius, elapsed) {
    const entry = sheetFor(enemy.blackHolePalette || "violet");
    if (!entry.ready) {
      drawFallback(ctx, enemy, radius, elapsed);
      return true;
    }

    const { width, height } = visualSize(radius);
    const seedOffset = ((enemy.visualSeed || enemy.phase || 0) / TAU) % 1;
    const normalized = ((elapsed / LOOP_SECONDS + seedOffset) % 1 + 1) % 1;
    const framePosition = normalized * FRAME_COUNT;
    const frameIndex = Math.floor(framePosition) % FRAME_COUNT;
    const nextIndex = (frameIndex + 1) % FRAME_COUNT;
    const blend = framePosition - Math.floor(framePosition);

    ctx.save();
    ctx.rotate((enemy.visualRoll || 0) * Math.PI / 1440);
    if (enemy.hit > 0) {
      ctx.filter = `brightness(${1 + Math.min(.48, enemy.hit * 3.1)}) saturate(1.08)`;
      ctx.shadowColor = "#fff";
      ctx.shadowBlur = 9;
    }
    drawFrame(ctx, entry.image, frameIndex, width, height, 1);
    if (blend > .002) drawFrame(ctx, entry.image, nextIndex, width, height, blend);
    ctx.restore();
    return true;
  }

  function spawnExplosion(particles, enemy, radius) {
    particles.push({
      type:"blackHoleDissolve", x:enemy.x, y:enemy.y, radius,
      blackHolePalette:enemy.blackHolePalette || "violet",
      visualRoll:enemy.visualRoll || 0, seed:enemy.visualSeed || enemy.phase || 1,
      life:1.9, maxLife:1.9
    });
  }

  function drawExplosion(ctx, particle) {
    const palette = PALETTES[particle.blackHolePalette] || PALETTES.violet;
    const entry = sheetFor(particle.blackHolePalette || "violet");
    const progress = 1 - particle.life / particle.maxLife;
    const ease = 1 - Math.pow(1 - progress, 3);
    const fade = Math.pow(1 - progress, 2.1);
    const { width, height } = visualSize(particle.radius);
    const frameIndex = Math.floor((((particle.seed || 0) / TAU) % 1 + 1) % 1 * FRAME_COUNT) % FRAME_COUNT;

    ctx.save();
    ctx.translate(particle.x, particle.y);
    ctx.rotate((particle.visualRoll || 0) * Math.PI / 1440);

    if (entry.ready) {
      ctx.filter = `blur(${(progress * 5.2).toFixed(2)}px)`;
      drawFrame(ctx, entry.image, frameIndex, width * (1 + ease * .07), height * (1 + ease * .07), fade);
      ctx.globalCompositeOperation = "lighter";
      for (let layer = 0; layer < 6; layer += 1) {
        const side = layer % 2 ? -1 : 1;
        const phase = particle.seed * .23 + layer * 2.17;
        ctx.save();
        ctx.translate(side * ease * particle.radius * (.22 + layer * .12), -ease * particle.radius * (.08 + layer * .055) + Math.sin(phase) * 5);
        ctx.filter = `blur(${(4 + progress * 11 + layer).toFixed(1)}px)`;
        drawFrame(ctx, entry.image, frameIndex, width * (1 + ease * (.05 + layer * .018)), height * (1 + ease * (.05 + layer * .018)), fade * (.07 + (6 - layer) * .012));
        ctx.restore();
      }
    }

    ctx.filter = "none";
    ctx.globalCompositeOperation = "lighter";
    ctx.lineCap = "round";
    for (let index = 0; index < 24; index += 1) {
      const phase = particle.seed * .31 + index * 2.399;
      const side = index % 2 ? -1 : 1;
      const spread = particle.radius * (.38 + ((index * 13) % 17) / 17 * 1.45) * ease;
      const x = side * spread + Math.sin(phase + progress * 4) * particle.radius * .16;
      const y = (index / 23 - .5) * particle.radius * 1.35 - progress * particle.radius * (.18 + .4 * ((index * 7) % 9) / 9);
      const w = particle.radius * (.16 + .34 * ((index * 11) % 13) / 13) * (1 + .55 * ease);
      ctx.globalAlpha = fade * (.08 + .18 * ((index * 17) % 19) / 19);
      ctx.strokeStyle = index % 3 === 0 ? palette.hot : index % 3 === 1 ? palette.mid : palette.cool;
      ctx.shadowColor = ctx.strokeStyle;
      ctx.shadowBlur = particle.radius * .11;
      ctx.lineWidth = Math.max(1.1, particle.radius * .025);
      ctx.beginPath();
      ctx.ellipse(x, y, w, particle.radius * .035, Math.sin(phase) * .2, Math.PI * .08, Math.PI * .92);
      ctx.stroke();
    }

    const afterglow = ctx.createRadialGradient(0, 0, 0, 0, 0, particle.radius * (1 + ease * 1.25));
    afterglow.addColorStop(0, rgba(palette.hot, .16 * fade));
    afterglow.addColorStop(.45, rgba(palette.mid, .11 * fade));
    afterglow.addColorStop(1, rgba(palette.cool, 0));
    ctx.globalAlpha = 1;
    ctx.fillStyle = afterglow;
    ctx.beginPath();
    ctx.arc(0, 0, particle.radius * (1 + ease * 1.25), 0, TAU);
    ctx.fill();
    ctx.restore();
  }

  window.EndlessBlackHoleEnemy = { PALETTES, draw, spawnExplosion, drawExplosion };
})();
