(() => {
  "use strict";

  const TAU = Math.PI * 2;
  const FRAME_WIDTH = 384;
  const FRAME_HEIGHT = 216;
  const FRAME_COLUMNS = 8;
  const FRAME_COUNT = 48;
  const PLAYBACK_FPS = 24;
  const DISPLAY_SAMPLE_FPS = 60;
  const TEMPORAL_TAPS = 3;
  const SOURCE_LOOP_SECONDS = FRAME_COUNT / PLAYBACK_FPS;
  const LOOP_SECONDS = 19.2;
  const MAX_GAME_BOSS_WIDTH = 360;
  const MAX_COLOSSAL_BOSS_WIDTH = 660;
  const HORIZON_RADIUS_X = .134;
  const HORIZON_RADIUS_Y = .225;
  const IS_PREVIEW = location.pathname.endsWith("black-hole-boss-preview.html");
  const MAX_LOADED_ASSETS = IS_PREVIEW ? 4 : 2;
  const MAX_POSE_DEGREES = 10;
  const DEG_TO_RAD = Math.PI / 180;
  const DISSOLVE_SECONDS = 1.25;

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
    const widthLimit = radius >= 100 ? MAX_COLOSSAL_BOSS_WIDTH : MAX_GAME_BOSS_WIDTH;
    const width = Math.min(widthLimit, Math.max(128, radius * 5.55));
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

  function drawFrameSlice(ctx, image, frameIndex, width, height, sliceIndex, sliceCount, offsetX, offsetY, alpha) {
    const sourceX = (frameIndex % FRAME_COLUMNS) * FRAME_WIDTH;
    const sourceY = Math.floor(frameIndex / FRAME_COLUMNS) * FRAME_HEIGHT;
    const sourceSliceHeight = FRAME_HEIGHT / sliceCount;
    const destinationSliceHeight = height / sliceCount;
    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.drawImage(
      image,
      sourceX, sourceY + sliceIndex * sourceSliceHeight, FRAME_WIDTH, sourceSliceHeight,
      -width / 2 + offsetX, -height / 2 + sliceIndex * destinationSliceHeight + offsetY,
      width, destinationSliceHeight + .5
    );
    ctx.restore();
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
    // Three-tap quadratic B-spline temporal reconstruction. The weights remain
    // positive and sum to one, so cloud brightness and velocity stay continuous
    // across source-frame boundaries without allocating more flipbook textures.
    const mix = position - Math.floor(position);
    return {
      prev:(index - 1 + FRAME_COUNT) % FRAME_COUNT,
      index,
      next:(index + 1) % FRAME_COUNT,
      prevWeight:.5 * (1 - mix) * (1 - mix),
      indexWeight:.75 - (mix - .5) * (mix - .5),
      nextWeight:.5 * mix * mix
    };
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
    ctx.imageSmoothingEnabled = true;
    ctx.imageSmoothingQuality = "high";
    applyPose(ctx, enemy);
    drawEventHorizon(ctx, width, height, palette);

    if (asset.sheetReady || (asset.sheet.complete && asset.sheet.naturalWidth)) {
      asset.sheetReady = true;
      const sample = frameSample(enemy, elapsed);
      drawFrame(ctx, asset.sheet, sample.prev, width, height, sample.prevWeight);
      drawFrame(ctx, asset.sheet, sample.index, width, height, sample.indexWeight);
      drawFrame(ctx, asset.sheet, sample.next, width, height, sample.nextWeight);
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
    const fade = Math.pow(1 - progress, 1.65);
    const { width, height } = visualSize(particle.radius);
    const frameIndex = Math.floor((((particle.seed || 0) / TAU) % 1 + 1) % 1 * FRAME_COUNT) % FRAME_COUNT;

    ctx.save();
    ctx.translate(particle.x, particle.y);
    applyPose(ctx, particle);
    drawEventHorizon(ctx, width * (1 + ease * .04), height * (1 + ease * .04), palette, fade);

    if (asset.sheetReady || (asset.sheet.complete && asset.sheet.naturalWidth)) {
      const expandedWidth = width * (1 + ease * .045), expandedHeight = height * (1 + ease * .045);
      drawFrame(ctx, asset.sheet, frameIndex, expandedWidth, expandedHeight, fade * .74);
      for (let slice = 0; slice < 6; slice += 1) {
        const side = slice % 2 ? -1 : 1;
        const phase = particle.seed * .19 + slice * 1.73;
        const driftX = side * ease * particle.radius * (.16 + slice * .045);
        const driftY = -ease * particle.radius * (.04 + slice * .018) + Math.sin(phase) * 2.5;
        drawFrameSlice(ctx, asset.sheet, frameIndex, expandedWidth, expandedHeight, slice, 6, driftX, driftY, fade * .24);
      }
    } else if (asset.posterReady || (asset.poster.complete && asset.poster.naturalWidth)) {
      drawPoster(ctx, asset.poster, width * (1 + ease * .045), height * (1 + ease * .045), fade);
    }

    ctx.globalCompositeOperation = "lighter";
    ctx.shadowBlur = 0;
    for (let index = 0; index < 7; index += 1) {
      const phase = particle.seed * .31 + index * 2.399;
      const side = index % 2 ? -1 : 1;
      const spread = particle.radius * (.3 + index * .13) * ease;
      const x = side * spread + Math.sin(phase) * particle.radius * .08;
      const y = (index / 6 - .5) * particle.radius * .92 - ease * particle.radius * (.08 + index * .025);
      const puff = particle.radius * (.055 + index * .008) * (1 + ease * .55);
      ctx.globalAlpha = fade * (.08 + (index % 3) * .035);
      ctx.fillStyle = index % 3 === 0 ? palette.hot : index % 3 === 1 ? palette.mid : palette.cool;
      ctx.beginPath();
      ctx.ellipse(x, y, puff * 1.8, puff, Math.sin(phase) * .3, 0, TAU);
      ctx.fill();
    }

    const afterglow = ctx.createRadialGradient(0, 0, 0, 0, 0, particle.radius * (1 + ease * 1.25));
    afterglow.addColorStop(0, rgba(palette.hot, .1 * fade));
    afterglow.addColorStop(.45, rgba(palette.mid, .07 * fade));
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
      frameCount:FRAME_COUNT, sourcePlaybackFps:PLAYBACK_FPS, displaySampleFps:DISPLAY_SAMPLE_FPS, temporalTaps:TEMPORAL_TAPS, sourceLoopSeconds:SOURCE_LOOP_SECONDS, loopSeconds:LOOP_SECONDS,
      dissolveSeconds:DISSOLVE_SECONDS,
      maxPoseDegrees:MAX_POSE_DEGREES,
      loaded:[...assets.values()].map((asset) => ({ name:asset.name, sheetReady:asset.sheetReady, posterReady:asset.posterReady }))
    };
  }

  window.EndlessBlackHoleEnemy = { PALETTES, preload, draw, spawnExplosion, drawExplosion, diagnostics };
})();
