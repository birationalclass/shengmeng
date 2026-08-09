(() => {
  "use strict";

  const TAU = Math.PI * 2;
  const FRAME_WIDTH = 384;
  const FRAME_HEIGHT = 216;
  const FRAME_COLUMNS = 8;
  const FRAME_COUNT = 48;
  const PLAYBACK_FPS = 24;
  const SOURCE_LOOP_SECONDS = FRAME_COUNT / PLAYBACK_FPS;
  const LOOP_SECONDS = 9.6;
  const MAX_GAME_BOSS_WIDTH = 360;
  const HORIZON_RADIUS_X = .134;
  const HORIZON_RADIUS_Y = .225;
  const IS_PREVIEW = location.pathname.endsWith("black-hole-boss-preview.html");
  const MAX_LOADED_ASSETS = IS_PREVIEW ? 4 : 2;
  const MAX_POSE_DEGREES = 10;
  const DEG_TO_RAD = Math.PI / 180;
  const DISSOLVE_SECONDS = 1.6;

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

  function visualSize(radius) {
    const width = Math.min(MAX_GAME_BOSS_WIDTH, Math.max(128, radius * 5.55));
    return { width, height:width * FRAME_HEIGHT / FRAME_WIDTH };
  }

  function poseAngle(value) {
    return Math.max(-MAX_POSE_DEGREES, Math.min(MAX_POSE_DEGREES, Number(value) || 0));
  }

  function applyPose(ctx, subject) {
    const yaw = poseAngle(subject.visualYaw);
    const pitch = poseAngle(subject.visualPitch);
    const roll = poseAngle(subject.visualRoll);
    const yawShear = Math.tan(yaw * DEG_TO_RAD) * .24;
    const pitchShear = Math.tan(pitch * DEG_TO_RAD) * .18;
    const scaleX = 1 - Math.abs(yaw) / MAX_POSE_DEGREES * .035;
    const scaleY = 1 - Math.abs(pitch) / MAX_POSE_DEGREES * .03;
    ctx.rotate(roll * DEG_TO_RAD);
    ctx.transform(scaleX, pitchShear, yawShear, scaleY, 0, 0);
  }

  const assets = new Map();

  function disposeAsset(asset) {
    asset.sheet.onload = null;
    asset.poster.onload = null;
    asset.sheet.src = "";
    asset.poster.src = "";
  }

  function trimAssets(currentName) {
    while (assets.size > MAX_LOADED_ASSETS) {
      const oldestName = assets.keys().next().value;
      if (oldestName === currentName) {
        const current = assets.get(oldestName);
        assets.delete(oldestName);
        assets.set(oldestName, current);
        continue;
      }
      const oldest = assets.get(oldestName);
      assets.delete(oldestName);
      disposeAsset(oldest);
    }
  }

  function loadAsset(name = "violet") {
    const paletteName = PALETTES[name] ? name : "violet";
    let asset = assets.get(paletteName);
    if (asset) {
      assets.delete(paletteName);
      assets.set(paletteName, asset);
      return asset;
    }

    const sheet = new Image();
    const poster = new Image();
    asset = { name:paletteName, sheet, poster, sheetReady:false, posterReady:false };
    sheet.decoding = poster.decoding = "async";
    sheet.onload = () => { asset.sheetReady = true; };
    poster.onload = () => { asset.posterReady = true; };
    sheet.src = new URL(`assets/black-hole-flipbook/black-hole-${paletteName}-clean.webp?v=20260810-v43-wide`, document.baseURI).href;
    poster.src = new URL(`assets/black-hole-flipbook/poster-${paletteName}-clean.webp?v=20260810-v43-wide`, document.baseURI).href;
    if (sheet.decode) sheet.decode().then(() => { asset.sheetReady = true; }).catch(() => {});
    if (poster.decode) poster.decode().then(() => { asset.posterReady = true; }).catch(() => {});
    assets.set(paletteName, asset);
    trimAssets(paletteName);
    return asset;
  }

  function preload(name) {
    loadAsset(name);
  }

  function drawEventHorizon(ctx, width, height, palette, alpha = 1) {
    const radiusX = width * HORIZON_RADIUS_X;
    const radiusY = height * HORIZON_RADIUS_Y;

    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.fillStyle = "#000";
    ctx.beginPath();
    ctx.ellipse(0, 0, radiusX, radiusY, 0, 0, TAU);
    ctx.fill();
    ctx.restore();
  }

  function drawFrame(ctx, image, frameIndex, width, height, alpha = 1) {
    const sourceX = (frameIndex % FRAME_COLUMNS) * FRAME_WIDTH;
    const sourceY = Math.floor(frameIndex / FRAME_COLUMNS) * FRAME_HEIGHT;
    ctx.save();ctx.globalAlpha=alpha;ctx.drawImage(image,sourceX,sourceY,FRAME_WIDTH,FRAME_HEIGHT,-width/2,-height/2,width,height);ctx.restore();
  }

  function drawPoster(ctx, image, width, height, alpha = 1) {
    ctx.save();ctx.globalAlpha=alpha;ctx.drawImage(image,-width/2,-height/2,width,height);ctx.restore();
  }

  function drawFallbackRing(ctx, width, height, palette, elapsed) {
    const pulse = .72 + Math.sin(elapsed * 1.4) * .06;
    ctx.save();
    ctx.strokeStyle = rgba(palette.mid, .42 * pulse);
    ctx.lineWidth = Math.max(1.25, width * .0045);
    ctx.beginPath();
    ctx.ellipse(0, 0, width * (HORIZON_RADIUS_X + .007), height * (HORIZON_RADIUS_Y + .014), 0, 0, TAU);
    ctx.stroke();
    ctx.restore();
  }

  function frameSample(enemy, elapsed) {
    const seedOffset = ((enemy.visualSeed || enemy.phase || 0) / TAU) % 1;
    const playbackRate = Math.max(.05, Math.min(2, enemy.blackHolePlaybackRate || 1));
    const normalized = ((elapsed * playbackRate / LOOP_SECONDS + seedOffset) % 1 + 1) % 1;
    const position = normalized * FRAME_COUNT;
    const index = Math.floor(position) % FRAME_COUNT;
    return { index, next:(index + 1) % FRAME_COUNT, mix:position - Math.floor(position) };
  }

  function draw(ctx, enemy, radius, elapsed) {
    const paletteName = enemy.blackHolePalette || "violet";
    const palette = PALETTES[paletteName] || PALETTES.violet;
    const asset = loadAsset(paletteName);
    const { width, height } = visualSize(radius);

    ctx.save();
    // The flipbook already contains the complete lens rim and bloom. The game
    // scene normally leaves a boss shadow active, so explicitly clear it here;
    // otherwise Canvas adds a second fluorescent outline around every frame.
    ctx.shadowBlur = 0;
    ctx.shadowColor = "transparent";
    applyPose(ctx, enemy);
    drawEventHorizon(ctx, width, height, palette);

    if (asset.sheetReady || (asset.sheet.complete && asset.sheet.naturalWidth)) {
      asset.sheetReady = true;
      const sample = frameSample(enemy, elapsed);
      drawFrame(ctx, asset.sheet, sample.index, width, height, 1 - sample.mix);
      drawFrame(ctx, asset.sheet, sample.next, width, height, sample.mix);
    } else if (asset.posterReady || (asset.poster.complete && asset.poster.naturalWidth)) {
      asset.posterReady = true;
      drawPoster(ctx, asset.poster, width, height);
    } else {
      drawFallbackRing(ctx, width, height, palette, elapsed);
    }

    // Damage text already provides hit feedback. Do not draw another ellipse:
    // sustained fire made that temporary hit ring look like part of the asset.
    ctx.restore();
    return true;
  }

  function spawnExplosion(particles, enemy, radius) {
    particles.push({
      type:"blackHoleDissolve", x:enemy.x, y:enemy.y, radius,
      blackHolePalette:enemy.blackHolePalette || "violet",
      visualYaw:poseAngle(enemy.visualYaw), visualPitch:poseAngle(enemy.visualPitch), visualRoll:poseAngle(enemy.visualRoll),
      seed:enemy.visualSeed || enemy.phase || 1,
      realTime:true, realStartedAt:performance.now(), realDuration:DISSOLVE_SECONDS,
      life:DISSOLVE_SECONDS, maxLife:DISSOLVE_SECONDS
    });
  }

  function drawExplosion(ctx, particle) {
    const paletteName = particle.blackHolePalette || "violet";
    const palette = PALETTES[paletteName] || PALETTES.violet;
    const asset = loadAsset(paletteName);
    const progress = 1 - particle.life / particle.maxLife;
    const ease = 1 - Math.pow(1 - progress, 3);
    const fade = Math.pow(1 - progress, 2.1);
    const { width, height } = visualSize(particle.radius);
    const frameIndex = Math.floor((((particle.seed || 0) / TAU) % 1 + 1) % 1 * FRAME_COUNT) % FRAME_COUNT;

    ctx.save();
    ctx.translate(particle.x, particle.y);
    applyPose(ctx, particle);
    drawEventHorizon(ctx, width * (1 + ease * .04), height * (1 + ease * .04), palette, fade);

    if (asset.sheetReady || (asset.sheet.complete && asset.sheet.naturalWidth)) {
      ctx.filter = `blur(${(progress * 4.8).toFixed(2)}px)`;
      drawFrame(ctx, asset.sheet, frameIndex, width * (1 + ease * .08), height * (1 + ease * .08), fade);
      ctx.globalCompositeOperation = "lighter";
      for (let layer = 0; layer < 6; layer += 1) {
        const side = layer % 2 ? -1 : 1;
        const phase = particle.seed * .23 + layer * 2.17;
        ctx.save();
        ctx.translate(side * ease * particle.radius * (.2 + layer * .115), -ease * particle.radius * (.08 + layer * .05) + Math.sin(phase) * 5);
        ctx.filter = `blur(${(4 + progress * 10 + layer).toFixed(1)}px)`;
        drawFrame(ctx, asset.sheet, frameIndex, width * (1 + ease * (.04 + layer * .016)), height * (1 + ease * (.04 + layer * .016)), fade * (.06 + (6 - layer) * .012));
        ctx.restore();
      }
    } else if (asset.posterReady || (asset.poster.complete && asset.poster.naturalWidth)) {
      drawPoster(ctx, asset.poster, width * (1 + ease * .08), height * (1 + ease * .08), fade);
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

  function diagnostics() {
    return {
      frameCount:FRAME_COUNT, sourcePlaybackFps:PLAYBACK_FPS, sourceLoopSeconds:SOURCE_LOOP_SECONDS, loopSeconds:LOOP_SECONDS,
      dissolveSeconds:DISSOLVE_SECONDS,
      maxPoseDegrees:MAX_POSE_DEGREES,
      loaded:[...assets.values()].map((asset) => ({ name:asset.name, sheetReady:asset.sheetReady, posterReady:asset.posterReady }))
    };
  }

  window.EndlessBlackHoleEnemy = { PALETTES, preload, draw, spawnExplosion, drawExplosion, diagnostics };
})();
