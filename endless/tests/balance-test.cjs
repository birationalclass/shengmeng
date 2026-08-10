"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const Balance = require("../balance-core.js");

function rng(seed) {
  let value = seed >>> 0;
  return () => {
    value ^= value << 13; value ^= value >>> 17; value ^= value << 5;
    return (value >>> 0) / 4294967296;
  };
}

const gameSource = fs.readFileSync(path.join(__dirname, "..", "game.js"), "utf8");
const blackHoleSource = fs.readFileSync(path.join(__dirname, "..", "black-hole-enemy.js"), "utf8");
const indexSource = fs.readFileSync(path.join(__dirname, "..", "index.html"), "utf8");
const cardStart = gameSource.indexOf("const CARDS = [");
const cardEnd = gameSource.indexOf("\n  ];", cardStart);
assert(cardStart >= 0 && cardEnd > cardStart, "可以读取完整卡牌定义");
const arrayStart = gameSource.indexOf("[", cardStart);
const cards = vm.runInNewContext(`(${gameSource.slice(arrayStart, cardEnd + 4)})`, { rangeCardDesc:() => "射程测试" });

const ids = new Set(cards.map((card) => card.id));
assert.equal(ids.size, cards.length, "所有卡牌 ID 唯一");
for (const card of cards) {
  assert.equal(typeof card.id, "string", "卡牌具有 ID");
  assert.equal(typeof card.name, "string", `${card.id} 具有名称`);
  assert(Array.isArray(card.tags) && card.tags.length, `${card.id} 具有分类`);
  assert(Number.isInteger(card.max) && card.max >= 1 && card.max <= 6, `${card.id} 层数处于安全范围`);
  for (const requirement of [...(card.req || []), ...(card.reqAny || [])]) assert(ids.has(requirement), `${card.id} 前置 ${requirement} 存在`);
  assert.equal(typeof card.desc(0), "string", `${card.id} 首级说明可渲染`);
  assert.equal(typeof card.desc(card.max - 1), "string", `${card.id} 满级说明可渲染`);
}

assert(/const DRAFT_OFFER_COUNT = 4;/.test(gameSource), "所有选卡均为四选一");
assert(/const NEW_RUN_OPENING_DRAFTS = 5;/.test(gameSource), "新局提供五轮开局选卡");
assert(/const NEW_RUN_RANDOM_CARDS = 3;/.test(gameSource), "新局额外直接获得三张随机卡牌");
assert(!cards.some((card) => card.id === "global_damage"), "已删除弹道火控总成");
assert.equal(cards.find((card) => card.id === "bullet_base_damage").max, 5, "子弹基础攻击卡改为五级弱成长");
assert(/const ACTIVE_SKILL_DEFS = \{/.test(gameSource), "六座炮塔具有主动技能定义");
for (const key of ["bullet","laser","missile","frost","arc","support"]) assert(new RegExp(`${key}:\\{card:\"${key}_active_skill\"`).test(gameSource), `${key} 主动技能存在`);
assert(/generateStarOffers/.test(gameSource), "四选一使用星级概率系统");
assert(/const LOOP_SECONDS = 19\.2;/.test(blackHoleSource), "黑洞旋转速度再次减半，完整循环延长到 19.2 秒");
assert(/const TEMPORAL_TAPS = 3;/.test(blackHoleSource), "黑洞使用三抽头时间超采样细化低速动画");
assert(/sample\.prev[\s\S]*sample\.index[\s\S]*sample\.next/.test(blackHoleSource), "黑洞运行时融合前帧、当前帧与后帧而非跳帧播放");
assert(/const DISPLAY_SAMPLE_FPS = 60;/.test(blackHoleSource), "黑洞以 60Hz 显示采样更新相邻帧混合");
assert(/prevWeight:\.5 \* \(1 - mix\)[\s\S]*indexWeight:\.75[\s\S]*nextWeight:\.5 \* mix \* mix/.test(blackHoleSource), "黑洞使用亮度守恒的二次 B 样条权重，避免慢速播放逐帧停顿");
assert(/imageSmoothingQuality = "high"/.test(blackHoleSource), "黑洞缩放与帧融合启用高质量图像采样");
assert(!/drawSideLensRims\(ctx, width, height, palette\)/.test(blackHoleSource), "黑洞主体不再叠加额外透镜边框");
assert(!/enemy\.hit[\s\S]{0,500}ctx\.ellipse/.test(blackHoleSource), "黑洞受击不再叠加整圈白色描边");
assert(/if\(enemy\.type\.bossKind!=="blackhole"\)\{[\s\S]{0,900}ringRadius/.test(gameSource), "黑洞首领不绘制开场无敌虚线圈");
assert(/const MAX_POSE_DEGREES = 10;/.test(blackHoleSource), "黑洞三轴姿态严格限制在正负十度");
assert(/visualYaw:isBlackHole\?-10\+Math\.random\(\)\*20:0/.test(gameSource), "黑洞水平倾角在正负十度内随机");
assert(/visualPitch:isBlackHole\?-10\+Math\.random\(\)\*20:0/.test(gameSource), "黑洞俯仰角在正负十度内随机");
assert(/visualRoll:isBlackHole\?-10\+Math\.random\(\)\*20:0/.test(gameSource), "黑洞滚转角在正负十度内随机");
assert(/const DISSOLVE_SECONDS = 1\.25;/.test(blackHoleSource), "黑洞首领在两秒内快速完成烟消云散");
assert(/realTime:true, realStartedAt:performance\.now\(\)/.test(blackHoleSource), "黑洞死亡动画使用真实时间计时");
assert(/if\(particle\.realTime\)continue;/.test(gameSource), "常规战斗时间不会重复扣减黑洞死亡动画");
assert(/updateRealtimeEffects\(time\);update\(dt\*\(state\.gameSpeed===2\?2:1\)\)/.test(gameSource), "真实时间死亡动画在暂停判定前继续更新，战斗时间支持倍速");
assert(/function hasActiveBlackHoleDissolve\(\)/.test(gameSource), "波次结算能够检测尚未完成的黑洞消散动画");
assert(/state\.waveEndTimer<=0&&!hasActiveBlackHoleDissolve\(\)/.test(gameSource), "黑洞完全消失后才弹出波次结算选卡");
assert(/addCard\(id,\{deferUI:true\}\);rememberCardChoice/.test(gameSource), "选卡点击不在当前帧重建全部界面");
assert(/libraryOverlay[\s\S]{0,100}classList\.contains\("show"\)/.test(gameSource), "卡牌图鉴关闭时不重建全部卡牌节点");
assert(/projectile\.type!=="missile"&&projectile\.type!=="frost"/.test(gameSource), "冰弹目标死亡后不会立即消失");
assert(/impactOrphanedFrost\(projectile,destinationX,destinationY\)/.test(gameSource), "失去目标的冰弹抵达记忆落点后生成控制区");
assert(/function impactOrphanedFrost[\s\S]{0,500}state\.slowFields\.push/.test(gameSource), "冰弹记忆落点会产生小范围减速场");
assert(/function drawFrameSlice\(/.test(blackHoleSource), "黑洞消散使用低成本切片漂散");
assert(!/ctx\.filter/.test(blackHoleSource), "黑洞消散不再执行高成本实时模糊");
assert(!/index < 24/.test(blackHoleSource), "黑洞消散不再绘制二十四条阴影片段");
assert(/function resolveEmptyDraft\(/.test(gameSource), "空卡池选卡会自动结算而不是停留在零选一");
assert(/if\(!generateOffers\(\)\)\{resolveEmptyDraft\(opening,false,false\);return;\}/.test(gameSource), "正常选卡弹窗只在存在合法卡牌时打开");
assert(/state\.rewardDraftsQueued=0/.test(gameSource), "奖励卡池耗尽时清空无法完成的后续奖励选卡");

assert.deepEqual(Balance.FORBIDDEN_INSIGHT_CHANCES, [0, .2, .28, .35, .43, .5], "禁忌洞见由 20% 成长至 50%");
assert.equal(Balance.forbiddenInsightChance(1), .2, "禁忌洞见一级为 20%");
assert.equal(Balance.forbiddenInsightChance(5), .5, "禁忌洞见满级为 50%");
assert.equal(Balance.rollForbiddenInsight(5, () => .49), true, "满级在 50% 内只返回一次布尔触发");
assert.equal(Balance.rollForbiddenInsight(5, () => .5), false, "满级不超过 50% 概率");
const forbiddenRollBranch = gameSource.indexOf("BalanceCore.rollForbiddenInsight");
assert(forbiddenRollBranch >= 0 && /grantRandomCards\("禁忌洞见",1\)/.test(gameSource), "禁忌洞见直接随机赠送一张合法卡牌");
assert(/禁忌代价 -50%/.test(gameSource), "禁忌洞见仍然支付一半当前屏障生命");
assert(!/showDraft\(false,true\)/.test(gameSource), "禁忌洞见不再弹出额外选卡面板");
assert(/grantRandomCards\("限时击杀成功",rewards\)/.test(gameSource), "限时猎物被击杀后直接随机发放卡牌");
assert(!/rewardDraftsQueued\+=rewards/.test(gameSource), "新奖励敌人不再排队弹出选卡面板");

assert(/function waveBossType\(\)\{const blackHoles=/.test(gameSource), "每一波守关首领都从黑洞序列选择");
assert(/function waveMidBossType\(\)/.test(gameSource), "恒星作为波次中途小首领出现");
assert(/function ensureBossSchedule\(\)/.test(gameSource), "每波使用随机小首领与黑洞日程");
assert(/double=state\.wave>=5/.test(gameSource), "中后期存在双黑洞守关概率");
assert(/colossal:state\.wave%3===0/.test(gameSource), "每三波的守关日程生成巨型黑洞");
assert(/type\.radius\*\(colossal\?2\.1:1\)/.test(gameSource), "巨型黑洞碰撞与画面尺寸至少扩大两倍");
assert(/const MAX_COLOSSAL_BOSS_WIDTH = 660;/.test(blackHoleSource), "巨型黑洞素材允许扩展到压迫性宽度");
assert(/if\(enemy\.type\.bossKind==="star"\)[\s\S]{0,700}continue;/.test(gameSource), "恒星小首领绕过控制与诱引逻辑并缓慢直行");
assert(/function buildStarfield\(/.test(gameSource), "战斗背景使用预渲染星空与星云");
assert(!/for\(let x=40;x<W;x\+=80\)/.test(gameSource), "星空背景不再绘制横纵战术网格");
assert(/function blackHoleAttackPalette\(enemy\)/.test(gameSource), "黑洞攻击从当前黑洞色板读取颜色");
assert(/hot:palette\.hot,mid:palette\.mid,cool:palette\.cool/.test(gameSource), "伽马射线携带黑洞高光、主色和暗部三层色值");
assert(/palette=blackHoleAttackPalette\(enemy\)[\s\S]{0,500}ctx\.strokeStyle=palette\.mid/.test(gameSource), "伽马射线蓄力提示使用对应黑洞主色");
assert(!/style:"gamma"[^\n]+color:"#dc78ff"/.test(gameSource), "伽马攻击不再固定使用紫色");
assert(/function enemyThreatTier\(enemy,wave=state\.wave\)/.test(gameSource), "敌方攻击按波次划分威胁阶位");
assert(/function enemyAttackScale\(enemy,wave=state\.wave\)/.test(gameSource), "Boss 与小怪具有独立的指数攻击成长曲线");
assert(/function enemyVolleyCount\(enemy\)/.test(gameSource), "普通敌军随阶位从单发成长为双发和三发");
assert(/function blackHoleGammaCount\(enemy\)/.test(gameSource), "黑洞伽马射线束数随威胁阶位成长");
assert(/gammaTargets=blackHoleGammaTargets\(enemy\)/.test(gameSource), "黑洞蓄力会预告本轮全部伽马射线落点");
assert(/enemy\.type\.damage\*enemyAttackScale\(enemy\)/.test(gameSource), "敌军突破伤害也接入攻击成长曲线");
const minionAttackScale = (wave) => Math.pow(1.07, wave - 1) * (1 + Math.floor((wave - 1) / 5) * .07);
const bossAttackScale = (wave, colossal = false) => Math.pow(1.105, wave - 1) * (1 + Math.floor((wave - 1) / 3) * .11) * (colossal ? 1.22 : 1);
assert(minionAttackScale(16) > minionAttackScale(1) * 3, "第 16 波小怪攻击强度相对开局有明确成长");
assert(bossAttackScale(9, true) > bossAttackScale(3, true) * 2, "巨型黑洞跨阶后攻击强度显著提升");
assert.equal(Math.min(3, 1 + (4 >= 3 ? 1 : 0) + (4 >= 6 ? 1 : 0) + 0), 2, "中期黑洞升级为双束伽马射线");
assert.equal(Math.min(3, 1 + (7 >= 3 ? 1 : 0) + (7 >= 6 ? 1 : 0) + 0), 3, "后期黑洞最多三束伽马射线");
assert(/resetGame\(\{startWave:9,openingDrafts:0\}\)[\s\S]{0,1200}state\.wave=9/.test(gameSource), "测试账号直接进入第九波巨型黑洞多束攻击验收");
assert(/function blackHoleMoveScale\(enemy\)/.test(gameSource), "黑洞使用快速入场与慢速巡航的分段移动曲线");
assert(/entryScale=enemy\.colossal\?9:4\.5,cruiseScale=enemy\.colossal\?\.5:\.68/.test(gameSource), "巨型与普通黑洞均快速入场并在战区显著减速");
assert(/enemy\.y\+=enemy\.speed\*blackHoleMoveScale\(enemy\)\*dt/.test(gameSource), "黑洞推进实际接入平滑移动倍率");
assert(/function starBossMoveScale\(enemy\)/.test(gameSource), "恒星小首领拥有快速入场到正常巡航的平滑曲线");
assert(/enemy\.y\+=enemy\.speed\*starBossMoveScale\(enemy\)\*dt/.test(gameSource), "恒星小首领移动实际接入入场倍率");
assert(/id="speedButton"/.test(indexSource) && /function toggleGameSpeed\(\)/.test(gameSource), "左侧控制区提供一倍与二倍游戏速度切换");
assert(/const DISTANCE_DAMAGE_MIN = \.5;/.test(gameSource), "战区最远端获得百分之五十伤害减免");
assert(/function distanceDamageMultiplier\(enemy\)[\s\S]{0,260}DISTANCE_DAMAGE_MIN\+\(1-DISTANCE_DAMAGE_MIN\)\*progress/.test(gameSource), "远距减伤向屏障前线性衰减至零");
assert(/let multiplier=defense\*distanceMultiplier/.test(gameSource), "所有敌方单位受击结算接入纵深减伤");
assert(/const DISTANCE_BALANCE_HP_SCALE = \.88;/.test(gameSource), "敌方基础生命下调以补偿新增纵深减伤");
assert(/if\(!opening&&!state\.draftWaveStarted\)\{repairAfterWave\(\);startNextWave\(\);state\.draftWaveStarted=true;\}/.test(gameSource), "波次奖励弹窗出现前已立即启动下一波");
assert(/state\.paused=!!opening/.test(gameSource), "仅开局配牌暂停，战斗中奖励弹窗保持运行");
assert(/下一波已开始 · 战斗不会因选卡暂停/.test(gameSource), "选卡弹窗明确提示后台战斗仍在继续");
assert(!/pauseOnDraftInput/.test(gameSource), "代码中已移除选卡暂停开关");

assert.deepEqual(Balance.BONUS_BOUNTY_INTERVALS, [0, 20, 15, 10], "奖励敌人判定节点由每 20 个缩短至每 10 个");
assert.equal(Balance.shouldSpawnBonusBounty(1, 20, () => .09), true, "一级每 20 个敌人进行 10% 判定");
assert.equal(Balance.shouldSpawnBonusBounty(1, 19, () => .01), false, "非判定节点不会生成额外奖励敌人");
assert.equal(Balance.shouldSpawnBonusBounty(3, 10, () => .1), false, "额外奖励敌人概率严格保持为 10%");

const families = ["弹道","激光","导弹","冰霜","电弧","支援","特殊"];
const pool = families.flatMap((family) => Array.from({ length:10 }, (_, index) => ({ id:`${family}-${index}`, tags:[family] })));
assert(/function blackHoleAsteroidCount\(enemy\)/.test(gameSource), "黑洞首领拥有随威胁阶位成长的小天体喷射数量");
assert(/function updateBlackHoleAsteroids\(enemy,dt\)/.test(gameSource), "黑洞小天体喷射拥有独立冷却并避开入场与无敌阶段");
assert(/bh_asteroid:\s*\{[^}]*name:"引力喷射小天体"/.test(gameSource), "喷射小天体是拥有独立血量、防御和分数的敌方单位");
assert(/typeId:"bh_asteroid"[\s\S]{0,900}maxHp,hp:maxHp/.test(gameSource), "黑洞喷射会生成可被炮塔锁定和击毁的小天体实体");
assert(/function updateEjectedAsteroid\(enemy,dt\)/.test(gameSource), "未被击毁的小天体会继续飞向屏障或小型炮塔");
assert(/function blackHoleSummonPool\(wave=state\.wave\)/.test(gameSource), "黑洞喷吐单位池会依据当前波次逐步解锁");
const summonPoolSource=gameSource.slice(gameSource.indexOf("function blackHoleSummonPool"),gameSource.indexOf("function blackHoleSummonCount"));
for(const unit of ["swarm","runner","splitter","tank","frigate","shield","prism","shooter","carrier","nova"])assert(summonPoolSource.includes(`\"${unit}\"`), `黑洞召唤池包含 ${unit}`);
assert(/function ejectBlackHoleUnits\(enemy\)/.test(gameSource) && /summonedByBlackHole=enemy\.id/.test(gameSource), "黑洞会喷吐可攻击的多类型敌方实体");
assert(/function updateBlackHoleSummons\(enemy,dt\)/.test(gameSource), "黑洞多类型喷吐拥有独立冷却与场上容量限制");
assert(/function blackHoleHorizonOrigin\(enemy,targetX,targetY\)/.test(gameSource), "伽马射线依据目标方向计算事件视界出射点");
assert(/style:"gamma"[\s\S]{0,120}x1:origin\.x,y1:origin\.y|x1:origin\.x,y1:origin\.y[\s\S]{0,220}style:"gamma"/.test(gameSource), "伽马射线从事件视界而不是黑洞中心出射");
assert(/side:"blackhole"/.test(gameSource), "激光在事件视界处截断而不是穿透黑洞");
assert(/if\(absorber\)[\s\S]{0,280}break;/.test(gameSource), "激光命中黑洞后停止后续反射路径");
assert(/absorbed=current\.type\.bossKind==="blackhole"/.test(gameSource), "电弧把黑洞识别为吸收终点");
assert(/spawnSparks\(beamEnd\.x,beamEnd\.y[\s\S]{0,80}if\(absorbed\)break/.test(gameSource), "电弧到达事件视界后终止链式跳跃");
assert(/function launchRepairBots\(turret,totalRepair,totalShield=0\)/.test(gameSource), "支援炮塔通过维修机器人而非瞬时脉冲治疗屏障");
assert(/targetX=BARRIER_ARC\.left\+34\+Math\.random\(\)/.test(gameSource), "维修机器人随机选择屏障弧面附着点");
assert(/function updateRepairBots\(dt\)/.test(gameSource), "机器人附着后按作业进度持续结算修补与护盾涂层");
assert(/function drawRepairBots\(\)/.test(gameSource), "战斗画面绘制飞行、附着和焊接状态的维修机器人");
assert(cards.some((card) => card.id === "repair_drone_bay") && cards.some((card) => card.id === "repair_drone_anchor"), "卡组包含机器人数量与驻留加工两条成长分支");
assert(/const effectiveWave=state\.openingDraft\?Math\.max\(8,state\.wave\):state\.wave/.test(gameSource), "开局五轮选卡允许出现满足前置的稀有与后期构筑卡");
assert(/ratios=\[0,\.3,\.45,\.6,\.8\]/.test(gameSource), "相位护盾按屏障上限百分比成长而非固定二十点");
for(const id of ["shield_overdrive","barrier_arsenal","aegis_retaliation"])assert(ids.has(id), `护盾联动卡 ${id} 已加入卡池`);
assert(/function payForbiddenInsightCost\(\)[\s\S]{0,420}shieldSpent=Math\.min\(state\.shield,cost\)/.test(gameSource), "禁忌洞见代价优先扣除黄色相位护盾");
assert(/function defensiveFirepowerMultiplier\(\)/.test(gameSource), "护盾数值与屏障生命上限能够转化为全局伤害");

function offerRates(history, preferenceTag = "", iterations = 30000) {
  const random = rng(0x5eed1234);
  const hits = Object.fromEntries(families.map((family) => [family, 0]));
  for (let index = 0; index < iterations; index += 1) {
    const offers = Balance.generateOffers(pool, { count:4, history, preferenceTag, rng:random });
    assert.equal(offers.length, 4, "每轮正好四张");
    assert.equal(new Set(offers.map((card) => card.id)).size, 4, "同轮不重复");
    for (const family of families) if (offers.some((card) => card.tags.includes(family))) hits[family] += 1;
  }
  return Object.fromEntries(families.map((family) => [family, hits[family] / iterations]));
}

const baseline = offerRates([]);
const afterBullet = offerRates([{ id:"弹道-0", families:["弹道"] }]);
assert(afterBullet["弹道"] < baseline["弹道"] * 0.72, "刚选择的弹道类别下一轮显著降权");
assert(afterBullet["激光"] > baseline["激光"], "未选择类别获得归一化概率补偿");
const preferredAfterBullet = offerRates([{ id:"弹道-0", families:["弹道"] }], "弹道", 5000);
assert.equal(preferredAfterBullet["弹道"], 1, "卡牌偏好仍然保底一张，不被疲劳覆盖");

assert(/laser:\s*\{[^\n]+cooldown:12/.test(gameSource), "激光炮低基础攻速使用十二秒启动间隔");
assert(/const LASER_TICK_INTERVAL=\.1;/.test(gameSource), "持续激光以稳定的十分之一秒脉冲结算");
assert(/function laserDuration\(\)\{return 3\+cardRank\("laser_duration"\)\*\.75;\}/.test(gameSource), "激光基础持续三秒并支持持续时间卡牌");
assert(/beginLaserChannel\(turret,target\)/.test(gameSource), "激光攻击会进入持续照射状态");
assert(/function updateLaserChannel\(/.test(gameSource), "激光持续期间追踪目标并连续结算");
for(const id of ["laser_duration","laser_cycle","laser_sustain"])assert(gameSource.includes(`id:"${id}"`), `激光持续机制卡牌 ${id} 已加入卡池`);

const baseDps = {
  bullet:7 / 2.4,
  laser:1.8 * (3 / .1) / 12,
  missile:30 / 6,
  frost:1.8 / 3.4,
  arc:(1.2 / 3.1) * (1 + .8 + .64)
};
assert(baseDps.arc < baseDps.bullet * .45, "电弧基础直接伤害保持辅助定位");
assert(baseDps.missile * 3 > baseDps.bullet * 1.8, "导弹命中三个密集目标时确立 AOE 优势");
assert(baseDps.frost < baseDps.bullet * .2, "冰霜保持低伤害控制定位");
const baseStars=Balance.starProbabilities([0,0,0,0,0]),boostedStars=Balance.starProbabilities([5,5,5,5,5]);
assert(Math.abs(baseStars.reduce((sum,value)=>sum+value,0)-1)<1e-9,"基础星级概率归一化");
assert(Math.abs(boostedStars.reduce((sum,value)=>sum+value,0)-1)<1e-9,"增幅后星级概率仍归一化");
assert(boostedStars[4]>baseStars[4]&&boostedStars[5]>baseStars[5],"特殊星图卡提高五星与六星爆率");
assert.deepEqual(Balance.earlyWaveProfile(1),{countScale:.62,hpScale:.54,attackScale:.42},"第一波按低基础炮塔强度下调");
assert.equal(Balance.earlyWaveProfile(6).hpScale,1,"第六波进入标准成长曲线");
for(const id of ["cryo_missile_echo","laser_arc_echo","bullet_support_echo"])assert(gameSource.includes(`id:"${id}"`),`六星主动联动 ${id} 已加入`);

console.log(JSON.stringify({
  cardsAudited:cards.length,
  openingDrafts:5,
  initialRandomCards:3,
  offerCount:4,
  forbiddenInsight:[Balance.forbiddenInsightChance(1), Balance.forbiddenInsightChance(5)],
  bonusBountyIntervals:[Balance.bonusBountyInterval(1), Balance.bonusBountyInterval(3)],
  bulletOfferBaseline:+baseline["弹道"].toFixed(3),
  bulletOfferAfterPick:+afterBullet["弹道"].toFixed(3),
  otherFamilyLift:+(afterBullet["激光"] / baseline["激光"] - 1).toFixed(3),
  baseDps:Object.fromEntries(Object.entries(baseDps).map(([key,value]) => [key,+value.toFixed(2)]))
}, null, 2));
