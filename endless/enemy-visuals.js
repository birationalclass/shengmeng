(() => {
  "use strict";

  const TAU = Math.PI * 2;

  function drawStar(ctx, enemy, radius, elapsed, colors = ["#fffbe0", "#ffd25d", "#ff713d"]) {
    const spin = elapsed * 0.16 + enemy.phase;
    const [core, mid, edge] = colors;

    ctx.save();
    const corona = ctx.createRadialGradient(0, 0, radius * 0.45, 0, 0, radius * 1.72);
    corona.addColorStop(0, `${mid}dc`);
    corona.addColorStop(0.52, `${edge}66`);
    corona.addColorStop(1, `${edge}00`);
    ctx.fillStyle = corona;
    ctx.beginPath();
    ctx.arc(0, 0, radius * 1.72, 0, TAU);
    ctx.fill();

    ctx.rotate(spin);
    ctx.lineCap = "round";
    for (let i = 0; i < 14; i += 1) {
      const angle = i * TAU / 14;
      const pulse = 0.5 + 0.5 * Math.sin(enemy.phase * 7 + i * 2.7 + elapsed * 0.9);
      const length = radius * (1.12 + pulse * 0.38);
      const bend = Math.sin(i * 3.1 + enemy.phase) * radius * 0.18;
      ctx.strokeStyle = i % 3 === 0 ? `${core}b8` : `${edge}78`;
      ctx.lineWidth = i % 3 === 0 ? 2.5 : 1.2;
      ctx.beginPath();
      ctx.moveTo(Math.cos(angle) * radius * 0.78, Math.sin(angle) * radius * 0.78);
      ctx.quadraticCurveTo(
        Math.cos(angle) * radius + bend * Math.sin(angle),
        Math.sin(angle) * radius - bend * Math.cos(angle),
        Math.cos(angle) * length,
        Math.sin(angle) * length
      );
      ctx.stroke();
    }
    ctx.restore();

    ctx.save();
    ctx.shadowColor = mid;
    ctx.shadowBlur = radius * 0.55;
    const surface = ctx.createRadialGradient(-radius * 0.28, -radius * 0.32, radius * 0.06, 0, 0, radius);
    surface.addColorStop(0, core);
    surface.addColorStop(0.24, mid);
    surface.addColorStop(0.68, edge);
    surface.addColorStop(1, colors[2] === "#3984ff" ? "#172d8b" : "#711c32");
    ctx.fillStyle = surface;
    ctx.beginPath();
    ctx.arc(0, 0, radius, 0, TAU);
    ctx.fill();

    ctx.beginPath();
    ctx.arc(0, 0, radius * 0.96, 0, TAU);
    ctx.clip();
    ctx.globalAlpha = 0.36;
    ctx.lineWidth = Math.max(1.4, radius * 0.035);
    for (let i = -3; i <= 3; i += 1) {
      ctx.strokeStyle = i % 2 ? core : mid;
      ctx.beginPath();
      ctx.ellipse(0, i * radius * 0.22, radius * (0.88 - Math.abs(i) * 0.06), radius * 0.12, Math.sin(spin + i) * 0.12, 0, TAU);
      ctx.stroke();
    }
    ctx.fillStyle = "rgba(42,10,50,.34)";
    for (const [x, y, size] of [[-0.34, -0.18, 0.12], [0.28, 0.12, 0.09], [-0.04, 0.36, 0.07]]) {
      ctx.beginPath();
      ctx.ellipse(x * radius, y * radius, size * radius, size * radius * 0.55, spin, 0, TAU);
      ctx.fill();
    }
    ctx.restore();

    ctx.save();
    ctx.strokeStyle = `${core}e0`;
    ctx.lineWidth = 1.6;
    ctx.beginPath();
    ctx.arc(0, 0, radius * 0.98, 0, TAU);
    ctx.stroke();
    ctx.restore();
  }

  function drawBlackHole(ctx, enemy, radius, elapsed) {
    if (window.EndlessBlackHoleEnemy?.draw(ctx, enemy, radius, elapsed)) return;
    const spin = elapsed * 0.12 + enemy.phase;
    const tilt = -0.16 + Math.sin(enemy.phase) * 0.1;

    ctx.save();
    ctx.rotate(tilt);
    ctx.shadowColor = "#ffb15c";
    ctx.shadowBlur = radius * 0.75;
    for (let i = 5; i >= 0; i -= 1) {
      const t = i / 5;
      ctx.strokeStyle = `rgba(${Math.round(255 - 35 * t)},${Math.round(225 - 105 * t)},${Math.round(150 - 40 * t)},${0.2 + 0.11 * (5 - i)})`;
      ctx.lineWidth = 2 + i * 1.8;
      ctx.beginPath();
      ctx.ellipse(0, 0, radius * (1.45 + i * 0.12), radius * (0.22 + i * 0.035), 0, 0, TAU);
      ctx.stroke();
    }
    const disk = ctx.createLinearGradient(-radius * 1.9, 0, radius * 1.9, 0);
    disk.addColorStop(0, "rgba(103,38,255,.08)");
    disk.addColorStop(0.22, "rgba(255,109,49,.76)");
    disk.addColorStop(0.48, "#fff4c4");
    disk.addColorStop(0.58, "#ffcf71");
    disk.addColorStop(1, "rgba(116,54,255,.08)");
    ctx.strokeStyle = disk;
    ctx.lineWidth = radius * 0.16;
    ctx.beginPath();
    ctx.ellipse(0, 0, radius * 1.68, radius * 0.31, 0, 0, TAU);
    ctx.stroke();
    ctx.restore();

    ctx.save();
    ctx.rotate(spin * 0.08);
    ctx.strokeStyle = "rgba(255,231,184,.72)";
    ctx.lineWidth = 2.2;
    ctx.beginPath();
    ctx.ellipse(0, -radius * 0.18, radius * 1.06, radius * 0.82, 0, Math.PI * 1.08, Math.PI * 1.92);
    ctx.stroke();
    ctx.beginPath();
    ctx.ellipse(0, radius * 0.18, radius * 1.06, radius * 0.82, 0, Math.PI * 0.08, Math.PI * 0.92);
    ctx.stroke();
    ctx.restore();

    const photon = ctx.createRadialGradient(0, 0, radius * 0.54, 0, 0, radius * 1.04);
    photon.addColorStop(0, "#000");
    photon.addColorStop(0.62, "#000");
    photon.addColorStop(0.73, "#130d24");
    photon.addColorStop(0.86, "#fff0c8");
    photon.addColorStop(0.91, "#b47cff");
    photon.addColorStop(1, "rgba(180,124,255,0)");
    ctx.fillStyle = photon;
    ctx.beginPath();
    ctx.arc(0, 0, radius * 1.04, 0, TAU);
    ctx.fill();
    ctx.fillStyle = "#000";
    ctx.beginPath();
    ctx.arc(0, 0, radius * 0.64, 0, TAU);
    ctx.fill();

    ctx.save();
    ctx.rotate(tilt);
    ctx.strokeStyle = "rgba(255,248,218,.9)";
    ctx.lineWidth = radius * 0.045;
    ctx.beginPath();
    ctx.ellipse(0, 0, radius * 1.66, radius * 0.3, 0, 0.05, Math.PI - 0.05);
    ctx.stroke();
    ctx.restore();
  }

  function drawBoss(ctx, enemy, radius, elapsed) {
    if (enemy.type.bossKind === "blackhole") drawBlackHole(ctx, enemy, radius, elapsed);
    else drawStar(ctx, enemy, radius, elapsed, enemy.type.starColors);

    ctx.save();
    ctx.textAlign = "center";
    ctx.font = "900 11px 'Microsoft YaHei UI'";
    ctx.fillStyle = "#f4fbff";
    ctx.shadowColor = enemy.type.color;
    ctx.shadowBlur = 8;
    const level = enemy.bossLevel ? ` LV.${enemy.bossLevel}` : "";
    ctx.fillText(`BOSS${level} · ${enemy.type.name}`, 0, -radius - 22);
    ctx.restore();
  }

  window.EndlessEnemyVisuals = { drawBoss, drawStar };
})();
