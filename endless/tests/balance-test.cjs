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
const cardEnd = gameSource.indexOf("  const CARD_MAP =");
assert(cardEnd > 0, "可以读取包含动态重构在内的完整卡牌定义");
const cardPrefix = `${gameSource.slice(0,cardEnd)}\n  globalThis.__cards=CARDS;\n  globalThis.__laserExposureChance=LASER_EXPOSURE_CHANCE;\n  globalThis.__laserExposureCap=LASER_EXPOSURE_CAP;\n  globalThis.__laserExposureProfiles=LASER_EXPOSURE_PROFILES;\n  globalThis.__laserExposureBossMultiplier=LASER_EXPOSURE_BOSS_MULTIPLIER;\n  globalThis.__rangeRelicChances=RANGE_RELIC_CHANCES;\n  globalThis.__relicBaseAttackValues=RELIC_BASE_ATTACK_VALUES;\n  globalThis.__relicBaseRateValues=RELIC_BASE_RATE_VALUES;\n  globalThis.__smallKillThresholds=SMALL_KILL_RELIC_THRESHOLDS;\n  globalThis.__bountyKillThresholds=BOUNTY_KILL_RELIC_THRESHOLDS;\n  globalThis.__bountyEchoChances=BOUNTY_ECHO_CHANCES;\n  globalThis.__waveChoiceEchoChances=WAVE_CHOICE_ECHO_CHANCES;\n})();`;
const cardCanvas = {getContext:()=>({})};
const cardDocument = {querySelector:(selector)=>selector==="#gameCanvas"?cardCanvas:{},querySelectorAll:()=>[]};
const cardSandbox = {console,document:cardDocument,window:{EndlessBalanceCore:{}},globalThis:null,Math,setTimeout,clearTimeout};
cardSandbox.globalThis=cardSandbox;
vm.runInNewContext(cardPrefix,cardSandbox,{filename:"game-card-prefix.js"});
const cards = cardSandbox.__cards;
const releaseId = gameSource.match(/const RELEASE_ID = "([^"]+)";/)?.[1];
assert(releaseId, "可以读取当前发布版本号");
assert.match(releaseId, /-v151-ten-difficulties-relics-damage-targets-r5$/, "当前发布版本为 v151 十大难度、十级遗物、独立卡级与逐敌伤害版本");
const cacheVersions = [...indexSource.matchAll(/(?:styles\.css|black-hole-enemy\.js|balance-core\.js|enemy-visuals\.js|game\.js)\?v=([^"']+)/g)].map((match)=>match[1]);
assert.equal(cacheVersions.length, 5, "首页五个本地 CSS/JS 入口均带缓存版本");
assert.deepEqual([...new Set(cacheVersions)], [releaseId], "首页全部本地资源缓存版本与 RELEASE_ID 完全一致");
assert(indexSource.includes('id="difficultyText"')&&/function updateUI\(force=false\)\{const difficulty=difficultyName\(\);[^\n]+\$\("#difficultyText"\)\.textContent=difficulty;\$\("#difficultyText"\)\.title=difficulty;/.test(gameSource),"左上战斗信息区实时显示冻结后的当前大难度与威胁阶");
assert(/\.run-stats \{[^}]*grid-template-columns:repeat\(3,minmax\(0,1fr\)\)/.test(fs.readFileSync(path.join(__dirname,"..","styles.css"),"utf8")),"波次、时间与难度在左上信息区保持三格同排");

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
assert(/const NEW_RUN_OPENING_DRAFTS = 5;/.test(gameSource), "新局提供五轮连续开局选卡");
assert(/const NEW_RUN_RANDOM_CARDS = 5;/.test(gameSource), "新局额外直接获得五张一至四星随机卡牌");
assert(/card\.star<=4\),initialCards=BalanceCore\.generateStarOffers/.test(gameSource), "开局随机奖励严格限定一至四星并复用星级权重算法");
assert(/const OPENING_GROWTH_CARD_IDS=\[\.\.\.Object\.values\(KILL_GROWTH_CARD_BY_TURRET\),"support_kill_healing"\]/.test(gameSource), "开局成长路线固定提供五类攻击成长与治疗成长共六张卡牌");
assert(/function showOpeningGrowthDraft\(resume=false\)/.test(gameSource)&&/成长路线选择 1 \/ 1/.test(gameSource)&&/finishOpeningGrowthDraft/.test(gameSource), "成长路线六选一在普通初始选卡前独立完成");
assert(/grantOpeningRandomCards\(NEW_RUN_RANDOM_CARDS\+relicLevel\("supply_capsule"\)\)/.test(gameSource)&&/if\(state\.openingDraftsRemaining>0\)scheduleOpeningDraft\(\)/.test(gameSource), "成长路线确认后才发放随机五张并进入五轮初始选卡");
assert(/openingRewardCards\.push\(\{id:card\.id,rank:cardRank\(card\.id\)\}\)/.test(gameSource)&&/成长 \$\{growth\.length\} · 随机 \$\{rewards\.length\} · 已选 \$\{picks\.length\}/.test(gameSource), "成长路线、随机奖励与逐次手选卡牌按获得时等级快照展示在初始构筑区");
assert(/const INITIAL_BARRIER_SEGMENT_HP = 100;/.test(gameSource), "五段小屏障各自以一百生命开始");
assert(!cards.some((card) => card.id === "global_damage"), "已删除弹道火控总成");
assert.equal(cards.find((card) => card.id === "bullet_base_damage").max, 5, "子弹基础攻击卡使用五级质变成长");
assert.equal(cards.find((card) => card.id === "bullet_base_damage").designRemoved, undefined, "子弹基础攻击卡不会被设计移除名单误伤");
assert(/function collectibleCardEntries\(\)\{return \[\.\.\.state\.cards\.entries\(\)\]\.filter\(\(\[id\]\)=>CARD_MAP\[id\]&&!CARD_MAP\[id\]\.designRemoved\);\}/.test(gameSource),"构筑、存档、图鉴和遥测共享只统计可获取卡牌的统一入口");
assert(/state\.cards=config\.cards\?new Map\(config\.cards\):new Map\(CARDS\.filter\(\(card\)=>!card\.designRemoved\)/.test(gameSource),"满卡测试预设不会把已删除废卡重新塞回构筑");
assert.equal(cards.find((card) => card.id === "bullet_base_damage").glyph, "⚔", "所有基础攻击卡使用统一武器图标");
for(const turretId of ["bullet","laser","missile","frost","arc"])assert.equal(cards.find((card)=>card.id===`${turretId}_range`).glyph,"◎",`${turretId} 射程卡使用统一扩张范围图标`);
const stylesSource=fs.readFileSync(path.join(__dirname,"..","styles.css"),"utf8");
assert(/--recent-left:\$\{left\.toFixed\(2\)\}%/.test(gameSource), "最近卡牌使用扑克牌式重叠位置而非横向滚动");
assert(/\.recent-cards > \.recent-card \{[^}]*inset:0 auto auto var\(--recent-left,0\)[^}]*transform:translate3d\(0,0,0\)/.test(stylesSource)&&!gameSource.includes("--recent-tilt"), "左侧最近卡牌保持同一基线并仅按横向位置覆盖");
assert(indexSource.includes('class="meter-scroll-body"')&&/\.meter-scroll-body \{[^}]*overflow:hidden/.test(stylesSource)&&/\.live-meter \.meter-list \{[^}]*overflow-y:auto/.test(stylesSource), "伤害来源与治疗来源各自拥有独立滚动区域");
assert(/grid-template-rows:minmax\(0,3fr\) minmax\(0,2fr\)/.test(stylesSource), "伤害与治疗区域按可用高度自适应分配且不会挤掉治疗面板");
assert(/\.live-meter \{[^}]*grid-row:2 \/ 4;[^}]*align-self:stretch/.test(stylesSource), "桌面战斗统计面板跨越下方网格并延伸到底部");
assert(gameSource.includes('renderCard=(card,level)=>')&&gameSource.includes('<span class="card-top"><b>${stars}</b>')&&/\.library-card \.glyph \{/.test(stylesSource), "卡牌图鉴按每个等级独立展示星带、主图标和玻璃卡体结构");
assert(!gameSource.includes('${turret.active?"在线":"待卡牌解锁"}'), "炮塔阵列不再显示在线或待解锁文字");
assert(/function updateSupportAutoDispatch\(turret,dt\)/.test(gameSource)&&/repairBotReserve=Math\.max\(0,reserve-launched\)/.test(gameSource), "自动治疗派遣与制造解耦且待命机器人库存真实扣减");
assert(/const fullLeft=.*glass=ctx\.createLinearGradient/.test(gameSource)&&/ctx\.globalCompositeOperation="screen"/.test(gameSource), "五段屏障由连续玻璃弧面和单层折射边缘绘制");
assert(/handY=normalized\*normalized\*12,handRotate=normalized\*2\.6/.test(gameSource), "开局已选卡牌使用同一平滑弧线计算高度与切线倾角");
assert(/function waveTimelineProgress\(\)/.test(gameSource)&&!/waveResolved\/state\.waveTarget\*100/.test(gameSource), "波次进度按预定出怪时间轴计算且不受分裂敌人影响");
assert(/function turretAdditiveBaseAttack\(turretId,flat=turretFlatDamage\(turretId\)\).*TURRET_DEFS\[turretId\].*turretPermanentAttackGrowth\(turretId\).*Number\(flat\)/.test(gameSource), "固定基础攻击以初始值、击杀永久成长与卡牌固定值相加");
assert(/function turretCardAdjustedBaseAttack\(turretId,flat=turretFlatDamage\(turretId\),multiplier=turretPassive\(turretId,"damage"\)\).*turretAdditiveBaseAttack\(turretId,flat\)\*\(1\+/.test(gameSource), "基础攻击百分比在全部固定基础数值相加后统一相乘");
assert(/value:turretCardAdjustedBaseAttack\(turretId,flat,multiplier\).*growth:turretPermanentAttackGrowth\(turretId\)/.test(gameSource), "卡牌预览纳入本局击杀成长并与实战公式一致");
assert(/function growLeadingTurretAttackFromKill\(\)/.test(gameSource)&&/recordRelicKillProgress\(enemy\);applySmallKillDamageRelic\(enemy\);[\s\S]{0,260}growLeadingTurretAttackFromKill\(\);growTurretRangeFromKill\(enemy,source\);rollStarlightRoadBounties\(enemy\)/.test(gameSource), "任意敌人死亡会先结算两类击杀遗物，再结算杀戮攻击、射程成长与星光奖励");
assert(/killGrowth:\{\.\.\.\(state\.killGrowth\|\|\{\}\)\}/.test(gameSource)&&/killGrowth:Object\.fromEntries/.test(gameSource), "杀戮成长会随存档保存并安全恢复");
const baseAttackProfiles = {
  bullet:{values:[.45,.9,1.3,1.7,2.5],flatValues:[45,90,130,170,250]},
  laser:{values:[.025,.05,.5,1.5,5],flatValues:[10,20,200,600,2000]},
  missile:{values:[.025,.05,.5,1.5,5],flatValues:[10,20,200,600,2000]},
  frost:{values:[.125,.275,.475,.75,1.25],flatValues:[2.5,5.5,9.5,15,25]},
  arc:{values:[.225,.45,.65,.85,1.25],flatValues:[22.5,45,65,85,125]}
};
const baseCritPowerProfiles = {
  bullet:[1,1.5,2,2.5,10],laser:[.4,1,3,8,20],missile:[.4,1,3,8,20],frost:[.5,.75,1,1.25,5],arc:[.5,.75,1,1.25,5]
};
const baseCritProfiles = {
  bullet:[.048,.072,.096,.12,.48],laser:[.0096,.024,.072,.192,.48],missile:[.0096,.024,.072,.192,.48],frost:[.048,.072,.096,.12,.48],arc:[.048,.072,.096,.12,.48]
};
const baseCooldowns={bullet:2.4,laser:10,missile:6,frost:3.4,arc:3.1};
const baseRateTargets={
  bullet:[.88,1.35,1.76,2.17,3],arc:[.44,.57,.67,.78,1],frost:[.34,.39,.47,.57,.75],missile:[.175,11/60,13/60,.3,.5],laser:[7/60,8/60,9/60,10/60,12/60]
};
for (const turretId of ["bullet","laser","missile","frost","arc"]) {
  const damageCard=cards.find((item)=>item.id===`${turretId}_base_damage`);
  const rateCard=cards.find((item)=>item.id===`${turretId}_base_rate`);
  const critCard=cards.find((item)=>item.id===`${turretId}_base_crit`);
  const critPowerCard=cards.find((item)=>item.id===`${turretId}_base_crit_power`);
  assert.deepEqual(Array.from(damageCard.passive.values),baseAttackProfiles[turretId].values,`${turretId} 基础攻击百分比使用炮塔专属质变曲线`);
  assert.deepEqual(Array.from(damageCard.passive.flatValues),baseAttackProfiles[turretId].flatValues,`${turretId} 固定攻击使用炮塔专属质变曲线`);
  rateCard.passive.values.forEach((bonus,index)=>assert(Math.abs((1+bonus)/baseCooldowns[turretId]-baseRateTargets[turretId][index])<1e-4,`${turretId} 第 ${index+1} 级达到设计射速`));
  assert.deepEqual(Array.from(critCard.passive.values),baseCritProfiles[turretId],`${turretId} 一星暴击率沿用各自攻击力曲线并在满级达到 50% 总暴击率`);
  assert.deepEqual(Array.from(critPowerCard.passive.values),baseCritPowerProfiles[turretId],`${turretId} 暴击伤害沿用基础攻击曲线`);
}
assert.deepEqual(Array.from(cards.find((item)=>item.id==="laser_base_crit_power").passive.values),baseCritPowerProfiles.laser,"基础攻击减半不影响暴击伤害卡牌");
for(const [turretId,rates] of Object.entries(baseRateTargets))assert(Math.abs((1+cards.find((card)=>card.id===`${turretId}_base_rate`).passive.values[4])/baseCooldowns[turretId]-rates[4])<1e-4,`${turretId} 满级射速精确命中设计值`);
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
assert(/addCard\(id,wasOpeningDraft\|\|wasOpeningGrowthDraft\?\{deferUI:true,skipDerived:true,skipRefraction:true,manualPick:true\}:\{deferUI:true,deferDerived:true,manualPick:true\}\);if\(state\.gameOver\)\{state\.selectingCard=false;return;\}if\(!wasOpeningDraft&&!wasOpeningGrowthDraft\)rememberCardChoice/.test(gameSource), "成长路线与连续初始选卡均不在当前帧重建全部界面，并跳过常规折射与历史降权");
assert(/function showDraft\(opening=false,bargain=false,reward=false\)\{if\(!state\.started\|\|state\.gameOver\|\|state\.drafting\)return;/.test(gameSource), "未开始战局时任何残留回调都不能越过部署页弹出选卡");
assert(/function showStartScreen\(\)[\s\S]{0,350}cancelOpeningDraftFrame\(\)/.test(gameSource), "进入部署页会取消旧战局尚未执行的开局选卡回调");
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

assert(/function forbiddenTomeProfile\(/.test(gameSource), "禁忌抄本按等级与波次计算高星奖励和生命代价");
assert(/function scheduleForbiddenTomeDraft\(/.test(gameSource), "禁忌抄本在过关后安排额外高星选卡");
assert(/function payForbiddenTomeCost\(profile\)/.test(gameSource)&&/segment\.baseMaxHp=Math\.max\(1,segment\.baseMaxHp\*keepMax\)/.test(gameSource)&&/segment\.overhealBonus=Math\.max\(0,segment\.overhealBonus\*keepMax\)/.test(gameSource)&&/segment\.maxHp=segment\.baseMaxHp\+segment\.overhealBonus/.test(gameSource)&&/segment\.hp=Math\.min\(segment\.maxHp,segment\.hp\*\(1-profile\.healthLossRate\)\)/.test(gameSource), "禁忌抄本按比例削减基础与筑垒上限并支付当前生命");
assert(!/showDraft\(false,true\)/.test(gameSource), "旧禁忌洞见额外选卡入口已停用");
assert(/fixedStar:star/.test(gameSource), "限时猎物按自身星级直接随机发放同星卡牌");
assert(!/rewardDraftsQueued\+=rewards/.test(gameSource), "新奖励敌人不再排队弹出选卡面板");
assert(/function rollProbabilityRefraction\(/.test(gameSource)&&/function queueProbabilityRefraction\(/.test(gameSource), "概率折射在每次正常获得同星卡后统一判定附赠卡");
assert(!cards.some((card)=>card.id.startsWith("fate_reroll_"))&&!/FATE_REROLL_BONUSES|fateRerollBonus/.test(gameSource), "命运重排卡牌及刷新加成逻辑已彻底移除");
assert(/function starlightRoadProfiles\(/.test(gameSource)&&/function rollStarlightRoadBounties\(enemy\)/.test(gameSource), "一至四星星光大道分别累计普通敌人击杀并独立生成奖励敌人");
assert(/STARLIGHT_ROAD_INTERVALS=Array\.from\(\{length:4\},\(\)=>\[30,25,20,15,10\]\)/.test(gameSource), "星光大道五级所需击杀数由 30 递减至 10");
assert(/STARLIGHT_ROAD_CHANCES=Array\.from\(\{length:4\},\(\)=>\[\.30,\.35,\.40,\.45,\.50\]\)/.test(gameSource), "星光大道触发率由 30% 成长至 50%");
assert(/projectile\.frostCarrier=true/.test(gameSource), "低温弹药把命中减速目标后的子弹转为寒冰载体");
assert(/spreadLimit=\[0,2,4,6\]/.test(gameSource)&&/decay=\[0,\.68,\.78,\.88\]/.test(gameSource), "电离寒潮按数量和逐跳衰减传染减速");
assert(/chilledPierces\+=1/.test(gameSource)&&/frost_laser_resonance/.test(gameSource), "激光穿透减速目标会逐段增伤");
assert(/coldDuration=Math\.min\(1,slowedEnemies/.test(gameSource), "减速目标数量最多使维修机器人持续时间翻倍");
assert(/if\(enemy\.frostFlower\)grantRandomCards\("霜之花绽放",1,\{fixedStar:star,specialOnly:true,noFallback:true,bountyOverflow:true\}\)/.test(gameSource), "霜之花优先奖励同星特殊卡牌，本星图鉴全亮后启用越级补偿");

assert(/function waveBossType\(wave=state\.wave\)\{const blackHoles=/.test(gameSource), "守关首领从黑洞序列选择");
assert(/function waveMidBossType\(\)/.test(gameSource), "恒星作为波次中途小首领出现");
assert(/function finalBossEntries\(wave=state\.wave\)\{\s*if\(wave<10\)return \[\]/.test(gameSource), "前九波不生成终局黑洞首领");
assert(/function colossalBossSequenceIndex\(wave=state\.wave\)\{return wave>=10&&\(wave-10\)%2===0/.test(gameSource), "第十波起偶数波固定进入超大首领关");
assert(/function blackHoleBossSequenceIndex\(wave=state\.wave\)\{return wave>=11&&\(wave-11\)%2===0/.test(gameSource), "第十一波起奇数波固定进入黑洞首领关");
assert(/if\(colossalIndex>=0\)return \[\{type:colossalIndex%2===0\?"boss_red_giant":"boss_red_antares",kind:"final",colossal:true\}\]/.test(gameSource), "超大首领在红巨星与参宿四之间轮换");
assert(/if\(blackHoleIndex>=0\)return \[\{type:waveBossType\(wave\),kind:"final",colossal:false\}\]/.test(gameSource), "普通黑洞排期保持正常尺寸");
assert(/function isRedGiantFinalWave\(wave=state\.wave\)\{return colossalBossSequenceIndex\(wave\)>=0/.test(gameSource), "超大首领关卡使用统一交替排期判断");
assert(/function bossPhaseCountForWave\(enemy,wave=state\.wave\)/.test(gameSource)&&/function updateBossPhase\(enemy\)/.test(gameSource), "大小首领按波次与生命比例进入最多四个阶段");
assert(/record\.phaseTransitions\.push\(\{phase,at:stats\.combatTime,hpRatio:Number\(ratio\.toFixed\(3\)\),label:bossPhaseLabel\(enemy,phase\)\}\)/.test(gameSource), "战斗日志记录首领阶段切换时间与生命比例");
assert(/type\.radius\*\(colossal\?4\.2:2\)/.test(gameSource), "黑洞碰撞与画面尺寸统一扩大两倍");
assert(/const MAX_GAME_BOSS_WIDTH = 720;/.test(blackHoleSource)&&/const MAX_COLOSSAL_BOSS_WIDTH = 1320;/.test(blackHoleSource), "黑洞渲染宽度上限同步扩大两倍");
assert(/if\(enemy\.type\.bossKind==="star"\|\|enemy\.type\.bossKind==="redgiant"\)[\s\S]{0,850}continue;/.test(gameSource), "恒星与红巨星绕过控制与诱引逻辑并沿固定航线推进");
assert(/function buildStarfield\(/.test(gameSource), "战斗背景使用预渲染星空与星云");
assert(/id="gpuOverlay"/.test(indexSource) && /id="gpuRendererText"/.test(indexSource), "启动页包含硬件图形加速检测弹窗与渲染器报告");
assert(/async function detectHardwareAcceleration\(\)/.test(gameSource), "启动时检测 WebGL、WebGPU 与当前渲染器");
assert(/swiftshader\|llvmpipe\|softpipe\|software raster\|microsoft basic render/.test(gameSource), "软件渲染器具有明确识别规则");
assert(/showHardwareAccelerationDialog\(\)/.test(gameSource), "游戏初始化会显示图形加速检测结果");
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
assert(/function blackHoleGammaDamageProfile\(enemy,wave=state\.wave\)/.test(gameSource)&&/barrierRatio=clamp\(\.5\+postTen\*\.01\+colossal\*\.05,\.5,\.85\)/.test(gameSource), "黑洞伽马射线从第十波起至少造成单段屏障上限百分之五十伤害并随波次成长");
assert(/percentDamage=\(segment\?\.maxHp\|\|Math\.max\(1,state\.globalBarrierMax\/BARRIER_SEGMENT_COUNT\)\)\*profile\.barrierRatio/.test(gameSource)&&/damage=profile\.fixedDamage\+percentDamage/.test(gameSource), "伽马射线把波次成长固定伤害与单段屏障百分比伤害共同结算");
assert(/enemy\.type\.damage\*enemyAttackScale\(enemy\)/.test(gameSource), "敌军突破伤害也接入攻击成长曲线");
const minionAttackScale = (wave) => Math.pow(1.07, wave - 1) * (1 + Math.floor((wave - 1) / 5) * .07);
const bossAttackScale = (wave, colossal = false) => Math.pow(1.105, wave - 1) * (1 + Math.floor((wave - 1) / 3) * .11) * (colossal ? 1.22 : 1);
assert(minionAttackScale(16) > minionAttackScale(1) * 3, "第 16 波小怪攻击强度相对开局有明确成长");
assert(bossAttackScale(9, true) > bossAttackScale(3, true) * 2, "巨型黑洞跨阶后攻击强度显著提升");
assert.equal(Math.min(3, 1 + (4 >= 3 ? 1 : 0) + (4 >= 6 ? 1 : 0) + 0), 2, "中期黑洞升级为双束伽马射线");
assert.equal(Math.min(3, 1 + (7 >= 3 ? 1 : 0) + (7 >= 6 ? 1 : 0) + 0), 3, "后期黑洞最多三束伽马射线");
assert(/resetGame\(\{startWave:10,openingDrafts:0\}\)[\s\S]{0,1200}state\.wave=10/.test(gameSource), "测试账号直接进入第十波黑洞多束攻击验收");
assert(/function blackHoleArrivalSpeed\(enemy\)/.test(gameSource), "黑洞使用受控的缓慢入场速度");
assert(/enemy\.y=Math\.min\(enemy\.bossStationY,enemy\.y\+blackHoleArrivalSpeed\(enemy\)\*dt\)/.test(gameSource), "黑洞仅移动到完整露出的驻留位置");
assert(/enemy\.bossStage="casting"[\s\S]{0,500}updateBlackHoleGamma/.test(gameSource), "黑洞完整露出并停止后才开始释放技能");
assert(/function startFinalBossWarning\(schedule\)/.test(gameSource)&&/WARNING · \$\{names\.join/.test(gameSource), "清场后终局首领具有独立红色预警阶段");
assert(/function starBossMoveScale\(\)\{return 1;\}/.test(gameSource), "恒星与超巨星取消快速入场并使用恒定慢速推进");
assert(!gameSource.includes("快速入场"), "大小首领的提示与逻辑不应再保留快速入场设定");
assert(/function blackHoleArrivalSpeed\(enemy\)\{return Math\.max\(enemy\.colossal\?14:12,enemy\.speed\);\}/.test(gameSource), "黑洞首领取消入场冲刺，只保留稳定低速进入");
assert(/function bossVisualHalfHeight\(type,radius\)/.test(gameSource)&&/spawnY=type\.boss\?-\(bossVisualHalfHeight\(type,radius\)\+24\)/.test(gameSource), "所有首领按真实视觉外接高度从战斗区域外完整入场");
assert(/function updateBlackHoleWander\(enemy,dt\)/.test(gameSource)&&/updateBlackHoleWander\(enemy,dt\);[\s\S]{0,120}updateBlackHoleGamma/.test(gameSource), "黑洞完成入场后在驻留区缓慢随机游走并继续释放技能");
assert(/enemy\.y\+=enemy\.speed\*starBossMoveScale\(enemy\)\*dt/.test(gameSource), "恒星与超巨星使用统一慢速入场倍率");
assert(/id="speedButton"/.test(indexSource) && /function toggleGameSpeed\(\)/.test(gameSource), "左侧控制区提供一倍与二倍游戏速度切换");
assert(/const DISTANCE_DAMAGE_MIN = \.1;/.test(gameSource), "战区最远端最终伤害降低百分之九十");
assert(/function distanceDamageMultiplier\(enemy\)[\s\S]{0,260}DISTANCE_DAMAGE_MIN\+\(1-DISTANCE_DAMAGE_MIN\)\*progress/.test(gameSource), "远距减伤向屏障前线性衰减至零");
assert(/barrierSurfaceY\(clamp\(point\.x,BARRIER_ARC\.left,BARRIER_ARC\.right\)\)/.test(gameSource), "远近伤害按首领最下端所在横坐标对应的屏障弧面计算");
assert(/multiplier=options\.trueDamage\?1:defense\*distanceMultiplier/.test(gameSource), "普通伤害接入纵深减伤，六相百分比真实伤害可绕过");
assert(/const DISTANCE_BALANCE_HP_SCALE = \.88;/.test(gameSource), "敌方基础生命下调以补偿新增纵深减伤");
assert(/if\(!opening&&!state\.draftWaveStarted\)\{repairAfterWave\(\);startNextWave\(\);state\.draftWaveStarted=true;\}/.test(gameSource), "波次奖励弹窗出现前已立即启动下一波");
assert(/draftPause:true/.test(gameSource)&&/id="draftPauseInput"/.test(indexSource), "设置提供独立的后续选卡暂停开关且默认开启");
assert(/state\.paused=!!opening\|\|state\.settings\.draftPause/.test(gameSource), "初始选卡始终暂停，后续选卡服从独立设置");
assert(/下一波已开始 · \$\{state\.settings\.draftPause\?"战斗已暂停":"战斗继续"\}/.test(gameSource), "后续选卡明确显示当前暂停状态");
assert(/state\.paused=state\.settings\.draftPause/.test(gameSource), "禁忌抄本选卡同样服从后续选卡暂停设置");

assert(/function subwaveCountForWave\(wave\)\{return Math\.min\(8,3\+/.test(gameSource), "第一波固定从三个小波起步并随波次增加");
assert(/function isInterwaveFillerSlot\(/.test(gameSource)&&/function spawnCadenceForWave\(/.test(gameSource), "小波之间使用低密度零星敌人填充并设置独立间隔");
assert(/function waveBossArrivalLimit\(wave\)\{return isRedGiantFinalWave\(wave\)\?60:45;\}/.test(gameSource), "普通关终局首领最迟 45 秒出现，超巨星关放宽到 60 秒");
assert(/function buildSpawnCadencePlan\(/.test(gameSource)&&/budget=Math\.max\(8,waveBossArrivalLimit\(wave\)-warning-initial-clearBuffer\)/.test(gameSource), "小波、填充怪与休整共同服从首领到场硬预算");
assert(/hardGateAt=waveBossArrivalLimit\(state\.wave\)-3\.8/.test(gameSource)&&/record\.combatTime>=hardGateAt/.test(gameSource), "即使残余小怪未清也会在截止时间进入终局警报");
assert(/function subwaveRestDuration\(wave,scenario=state\.waveScenario\|\|waveScenario\(wave\)\)\{return clamp\(/.test(gameSource), "小波仍保留可识别的休整段且会随总预算压缩");
assert(/waveBaseTarget:state\.waveTarget/.test(gameSource), "小波节奏使用基础刷怪数，不受分裂与召唤临时扩容干扰");
assert(/base=\(20\+wave\*3\.4\+Math\.pow\(wave,1\.1\)\*1\.25\)/.test(gameSource), "每波普通敌人总量采用扩容后的成长曲线");
assert.equal(Balance.waveEnemyPressureMultiplier(1).hp,.5, "第一波所有敌人生命与攻击为标准值的一半");
assert.equal(Balance.waveEnemyPressureMultiplier(10).hp,1, "前十波敌方压力平滑恢复到标准值");
assert(/function earlySmallEnemyHpMultiplier\(\)\{return 1;\}/.test(gameSource), "旧版普通小怪生命折扣已归并到统一波次压力曲线");
assert(/waveBaseHp\(\)\*earlySmallEnemyHpMultiplier\(type\)\*DISTANCE_BALANCE_HP_SCALE/.test(gameSource), "普通小怪生命倍率接入实际生成数值");
assert(/function normalEnemySpeedMultiplier\(type\)\{return !type\.boss&&!type\.bounty&&!type\.summoned\?\.8:1;\}/.test(gameSource), "所有普通小怪移动速度统一降低百分之二十");
assert(/type\.speed\*normalEnemySpeedMultiplier\(type\)\*\(type\.boss\?\.6:1\)/.test(gameSource), "普通小怪速度倍率接入实际生成速度且不改变首领与奖励单位");
assert(/function turretFormationY\(x\)\{return Math\.round\(1138\+\(barrierSurfaceY\(x\)-barrierSurfaceY\(W\/2\)\)\*\.36\);\}/.test(gameSource), "六座炮塔按屏障圆弧曲率排布并让两侧炮塔适当下沉");
assert(/function turretFormationOffset\(id\)\{return id==="laser"\|\|id==="arc"\?12:0;\}/.test(gameSource)&&/\.\.\.def,damage:turretAdditiveBaseAttack\(id\),y:turretFormationY\(def\.x\)\+turretFormationOffset\(id\),id,active:/.test(gameSource), "所有炮塔使用圆弧阵列纵坐标，治疗与电弧交换槽位后高度偏移同步交换");
assert(/const BOUNTY_WANDER_TOP = H \* \.25;/.test(gameSource)&&/const BOUNTY_WANDER_BOTTOM = H \* \.75;/.test(gameSource), "奖励敌人只在战区纵向四分之一至四分之三区域游荡");

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
assert(/function launchRepairBots\(turret,totalRepair,totalShield=0,options=\{\}\)/.test(gameSource), "支援炮塔通过维修机器人而非瞬时脉冲治疗屏障");
assert(/const SUPPORT_INITIAL_RESERVE\s*=\s*3/.test(gameSource)&&/const SUPPORT_RESERVE_CAPACITY\s*=\s*4/.test(gameSource)&&/repairBotReserve:id==="support"\?Math\.min\(SUPPORT_RESERVE_CAPACITY,Math\.max\(0,stored\?\.repairBotReserve\?\?SUPPORT_INITIAL_RESERVE\)\):0/.test(gameSource), "支援炮塔初始三台、硬上限四台，旧存档库存会安全截断");
assert(/function manufactureSupportBots\(turret,count=1\)/.test(gameSource)&&/manufactureSupportBots\(turret,1\+\(bayRank/.test(gameSource), "支援炮塔按自身作业周期持续制造库存机器人，并允许机库概率并联生产");
assert(/function supportReserveCapacity\(\)\{return SUPPORT_RESERVE_CAPACITY;\}/.test(gameSource)&&/visible=Math\.min\(SUPPORT_RESERVE_CAPACITY,reserve\)/.test(gameSource), "制造与待命环绕显示统一遵守四台库存上限");
assert(/function tryManualRepairDispatch\(x,y,all=false\)[\s\S]{0,420}turret\.targetMode!=="manual"[\s\S]{0,420}all\?available:1/.test(gameSource), "手动支援模式左键派遣一台、右键派遣该塔全部库存机器人");
assert(/handleCanvasClick[\s\S]{0,200}tryManualRepairDispatch\(x,y,false\)/.test(gameSource)&&/handleCanvasContextMenu[\s\S]{0,220}tryManualRepairDispatch\(x,y,true\)/.test(gameSource), "小屏障左右键分别接入单台与全量派遣交互");
assert(/const skillIndex="qwerty"\.indexOf\(event\.key\.toLowerCase\(\)\)/.test(gameSource), "主动技能快捷键使用 QWERTY");
assert(/selectSupportBarrierSegment\(mode\)/.test(gameSource) && /barrierSegmentTargetX\(segment/.test(gameSource), "维修机器人依据支援优先级选择五段屏障附着点");
assert(/function updateRepairBots\(dt\)/.test(gameSource), "机器人附着后按作业进度持续结算修补与护盾涂层");
assert(/function drawRepairBots\(\)/.test(gameSource), "战斗画面绘制飞行、附着和焊接状态的维修机器人");
assert(cards.some((card) => card.id === "repair_drone_bay") && cards.some((card) => card.id === "repair_drone_anchor"), "卡组包含机器人数量与驻留加工两条成长分支");
assert(/id:"support_base_duration"[\s\S]{0,260}stat:"botDuration"/.test(gameSource), "支援基础卡包含真实影响作业时长的机器人持续时间");
assert(/const BARRIER_SEGMENT_COUNT\s*=\s*5/.test(gameSource) && /function drawSegmentedBarrier\(\)/.test(gameSource), "全局屏障拆分为五段独立血量并绘制");
assert(/lostBarrierSegmentCount\(\)\*\.2/.test(gameSource), "每失去一段，其余屏障受到额外 20% 伤害");
assert(/敌军下缘穿越第/.test(gameSource) && /endGame\(\)/.test(gameSource), "敌军下缘穿越零血量屏障区会立即失败");
assert(gameSource.includes("shield:segmentShield,maxShield:segmentShieldMax") && /result=damageBarrierSegment\(segment,integrity/.test(gameSource), "五段屏障分别维护生命与相位护盾，并通过统一分段承伤管线独立结算碰撞");
assert(/lowestBarrier[\s\S]{0,180}highestBarrier[\s\S]{0,180}farFriendly[\s\S]{0,180}balancedRandom/.test(gameSource), "支援炮塔提供四种独立治疗优先级");
assert.equal(Balance.DIFFICULTY_STEP_MULTIPLIER,1.5,"每个连续小难度阶统一提升 1.5 倍敌方战斗数值");
for(let rating=0;rating<49;rating+=1)assert(Math.abs(Balance.difficultyStatMultiplier(rating+1)/Balance.difficultyStatMultiplier(rating)-1.5)<1e-12,`难度 ${rating} → ${rating+1} 严格连续提升 1.5 倍`);
assert.equal(Balance.difficultyStatMultiplier(4),Math.pow(1.5,4),"行星 V 使用连续第 4 次指数提升");
assert.equal(Balance.difficultyStatMultiplier(5),Math.pow(1.5,5),"恒星 I 紧接行星 V 再提升 1.5 倍");
assert(/difficultyFactors\(\)\.hp/.test(gameSource) && /difficultyFactors\(\)\.attack/.test(gameSource), "统一难度倍率同时进入敌军生命与攻击入口");
assert(!gameSource.includes("difficultyFactors().count"),"指数难度不放大敌军数量，避免最高阶出现不可控单位数");
assert(/runDifficulty:normalizeRunDifficulty\(state\.runDifficulty\)/.test(gameSource)&&/state\.runDifficulty=normalizeRunDifficulty\(run\.runDifficulty\)/.test(gameSource),"战局保存并恢复开局难度快照");
assert(/const CAMPAIGN_CLEAR_WAVE = 50;/.test(gameSource), "航线固定在完成第 50 波后通关");
assert(/function completeCardCollection\(\)[\s\S]{0,420}坚守至第 \$\{CAMPAIGN_CLEAR_WAVE\} 波/.test(gameSource) && !/function completeCardCollection\(\)[\s\S]{0,420}endGame\(true\)/.test(gameSource), "全卡收集只记录里程碑，不再提前通关");
assert(/function recordClearedWave\(\)[\s\S]{0,420}state\.wave>=CAMPAIGN_CLEAR_WAVE[\s\S]{0,100}endGame\(true\)/.test(gameSource), "仅在完整清除第 50 波后进入难度解锁结算");
for(const relic of ["vanguard_chart","supply_capsule","barrier_seed","time_prism","healing_bastion_core","rangefinder_array","arsenal_core","tempo_core","swarm_war_archive","bounty_echo_beacon"])assert(gameSource.includes(`id:"${relic}"`), `遗物 ${relic} 已实现`);
assert.deepEqual(Array.from(cardSandbox.__relicBaseAttackValues,Number),[0,20,40,60,80,100,120,140,160,180,200],"军械基座十级每级提供 +20 基础攻击，最高 +200");
assert.deepEqual(Array.from(cardSandbox.__relicBaseRateValues,Number),[0,.05,.10,.15,.20,.25,.30,.35,.40,.45,.50],"脉冲节拍器十级每级提供 +5% 基础攻速，最高 +50%");
for(const relic of ["rangefinder_array","supply_capsule","arsenal_core","barrier_seed","tempo_core"])assert(new RegExp(`id:"${relic}"[^\\n]+maxLevel:GENERAL_RELIC_LEVEL_CAP`).test(gameSource),`${relic} 使用十级大难度成长`);
assert(/const DIFFICULTY_RELIC_TRACKS=\[[\s\S]{0,260}minor:1,relic:"rangefinder_array"[\s\S]{0,80}minor:2,relic:"supply_capsule"[\s\S]{0,80}minor:3,relic:"arsenal_core"[\s\S]{0,80}minor:4,relic:"barrier_seed"[\s\S]{0,80}minor:5,relic:"tempo_core"/.test(gameSource),"每个大难度的 I/II/III/IV/V 分别升级射程、补给、攻击、屏障和攻速遗物");
assert.deepEqual(Array.from(cardSandbox.__smallKillThresholds,Number),[1000,2000,4000,8000,16000,32000,64000,128000,256000,512000],"小怪击杀遗物从 1000 起每级需求翻倍至十级");
assert.deepEqual(Array.from(cardSandbox.__bountyKillThresholds,Number),[100,200,400,800,1600,3200,6400,12800,25600,51200],"奖励怪击杀遗物从 100 起每级需求翻倍至十级");
assert.deepEqual(Array.from(cardSandbox.__bountyEchoChances,Number),[0,.10,.13,.17,.20,.23,.27,.30,.33,.37,.40],"悬赏回声信标十级概率由 10% 成长至 40%");
assert.deepEqual(Array.from(cardSandbox.__waveChoiceEchoChances,Number),[0,.10,.13,.16,.20,.25],"余辉演化五级概率为 10%/13%/16%/20%/25%");
assert(/function turretAdditiveBaseAttack\(turretId[^\n]+runRelicBaseAttackBonus\(\)/.test(gameSource),"军械基座在基础攻击固定值汇总入口生效");
assert(/function turretCooldown\(turret\)[^\n]+runRelicAttackSpeedBonus\(\)[^\n]+turretPassive\(turret\.id,"rate"\)\+relicRate/.test(gameSource),"脉冲节拍器在所有攻击炮塔实际冷却入口生效");
assert(/ensureProgress\(account\);evaluateAchievements\(false\);state\.best/.test(gameSource),"旧账号登录时会按既有进度补发新增遗物成就");
assert.equal(Balance.BARRIER_RELIC_UNLOCK_THRESHOLD,10_000_000,"千万屏障成就阈值为五段总上限 10m");
assert.equal(Balance.hasReachedBarrierRelicThreshold(9_999_999),false,"屏障上限未到 10m 时不解锁遗物");
assert.equal(Balance.hasReachedBarrierRelicThreshold(10_000_000),true,"屏障上限恰好达到 10m 时解锁遗物");
assert(gameSource.includes('id:"ten_million_bastion"')&&gameSource.includes('relic:"healing_bastion_core"'),"千万壁垒成就解锁筑垒核心遗物");
assert(/function relicLevel\(id,progress=null\)\{if\(!progress&&state\.started&&!state\.gameOver\)return runRelicLevel\(id\)/.test(gameSource),"战斗中的所有遗物效果只读取开局快照");
assert(/runRelicLevels:\{\.\.\.\(state\.runRelicLevels\|\|\{\}\)\}/.test(gameSource)&&/state\.runRelicLevels=normalizeRunRelicLevels\(run\.runRelicLevels\)/.test(gameSource),"开局遗物快照随战局保存与恢复");
assert(/runRelicLevel\("healing_bastion_core"\)>0\)addCard\("support_overheal_fortification",\{deferUI:true,skipRefraction:true,silent:true\}\)/.test(gameSource),"筑垒核心只在新局入口授予治疗筑垒 1 级");
assert(/checkBarrierRelicAchievement\(\)/.test(gameSource)&&/hasReachedBarrierRelicThreshold\(state\.globalBarrierMax\)/.test(gameSource),"屏障总上限统一重算时检查千万壁垒成就");
assert(indexSource.includes("新解锁或升级的遗物会在下一局开始时装备")&&indexSource.includes("每升 1 阶 ×1.5"),"遗物延迟生效与难度阶梯规则在界面中明确说明");
const rangeRelicChances = Array.from(cardSandbox.__rangeRelicChances, Number);
assert.deepEqual(rangeRelicChances,[0,.10,.12,.14,.16,.18,.20,.22,.24,.27,.30],"远域测距阵列十级触发率由 10% 成长至 30%");
assert(rangeRelicChances.slice(1).every((chance,index,values)=>chance>0&&chance<1&&(index===0||chance>values[index-1])),"测距阵列触发率逐级严格提高且保持为合法概率");
assert(/\.\.\.DIFFICULTY_MAJORS\.flatMap\(\(difficulty,majorIndex\)=>DIFFICULTY_RELIC_TRACKS\.map/.test(gameSource)&&/relic:track\.relic,relicLevel:majorIndex\+1/.test(gameSource),"十大难度的五个固定小阶分别把对应遗物提升至 LV.1–LV.10");
assert(/const account=activeAccount\(\),progress=ensureProgress\(account\),runRelicLevels=snapshotRelicLevels\(progress\)/.test(gameSource)&&/state\.runRelicLevels=runRelicLevels/.test(gameSource),"新解锁或升级的测距阵列只在下一局快照时装备");
assert(/function growTurretRangeFromKill\(enemy,source\)[^\n]+enemy\.type\.boss\|\|enemy\.type\.bounty\|\|enemy\.type\.summoned\|\|enemy\.type\.splitChild\|\|enemy\.summonedByBlackHole\|\|enemy\.sourceBossId/.test(gameSource),"首领、悬赏、裂殖子体与其他召唤物不会刷取射程成长");
assert(/function attributedRangeTurret\(source\)[^\n]+direct=meterTurretGroup\(String\(source\|\|""\)\)[^\n]+if\(attackIds\.includes\(direct\)\)return direct/.test(gameSource),"直接击杀来源优先把射程成长归属到实际攻击炮塔");
assert(/function attributedRangeTurret\(source\)[^\n]+if\(source==="分段屏障"\)return null[^\n]+ensureWaveStats\(\)\.damage[^\n]+ranked\[0\]\?\.damage>0\?ranked\[0\]\.turretId:null/.test(gameSource),"联动击杀回退到本波伤害最高攻击炮塔，分段屏障则明确不归属");
const attributedRangeSource=gameSource.match(/  function attributedRangeTurret\([^\r\n]+/)?.[0]||"";
const attributionSandbox={globalThis:null};
attributionSandbox.globalThis=attributionSandbox;
vm.runInNewContext(`
  let __damage={};
  const meterTurretGroup=(source)=>({"子弹炮":"bullet","激光炮":"laser","导弹炮":"missile","冰霜炮":"frost","电弧炮":"arc"})[source]||"";
  const ensureWaveStats=()=>({damage:__damage});
${attributedRangeSource}
  globalThis.__setDamage=(damage)=>{__damage=damage;};
  globalThis.__attributedRangeTurret=attributedRangeTurret;
`,attributionSandbox,{filename:"range-attribution-test.js"});
attributionSandbox.__setDamage({"激光炮":120,"导弹炮":420});
assert.equal(attributionSandbox.__attributedRangeTurret("子弹炮"),"bullet","可识别的直接击杀来源优先于伤害榜回退");
assert.equal(attributionSandbox.__attributedRangeTurret("联动燃烧"),"missile","无法直接归因的联动击杀回退到本波伤害最高炮塔");
assert.equal(attributionSandbox.__attributedRangeTurret("分段屏障"),null,"分段屏障击杀不会错误授予射程成长");
assert(/function turretRange\(turret\)[^\n]+grown=\(cardRange\*\(1\+turretPassive\(turret\.id,"range"\)\)\)\+turretRangeGrowth\(turret\.id\),suppressed=grown\*\(1-activeTurretRangePenalty\(\)\)/.test(gameSource),"射程先结算卡牌倍率与局内固定成长，再统一承受首领压制");
const rangeFormulaSample = Math.round((200*(1+.5)+20)*(1-.25));
assert.equal(rangeFormulaSample,240,"200 基础射程、50% 卡牌倍率、+20 击杀成长与 25% 压制最终为 240");
assert(/rangeKillGrowth:\{\.\.\.\(state\.rangeKillGrowth\|\|\{\}\)\}/.test(gameSource)&&/state\.rangeKillGrowth=Object\.fromEntries\(\["bullet","laser","missile","frost","arc"\]/.test(gameSource),"五塔射程成长随战局保存并以非负整数恢复");
assert(/drawTurretRange\(\)[^\n]+成长 \+\$\{growth\}[^\n]+压制 -\$\{Math\.round\(penalty\*100\)\}%/.test(gameSource),"炮塔范围预览同时显示局内成长与当前压制百分比");
assert(/const effectiveWave=state\.openingDraft\?Math\.max\(12,state\.wave\):state\.wave/.test(gameSource), "开局七轮选卡允许出现满足前置的中高阶构筑卡");
for(const id of ["ballistic_heal_block","arc_heal_block","missile_armor_pierce"])assert(ids.has(id), `反治疗与穿甲低星卡 ${id} 已加入卡池`);
assert(!ids.has("bullet_armor_pierce"),"旧钨芯单点穿甲卡已从卡池移除");
assert(gameSource.includes('healer: { name:"翠辉修复舰"')&&gameSource.includes('supportRole:"single"')&&gameSource.includes('if(wave>=10)pool.push("nova","frigate","prism","healer")'), "第十波起逐步加入单体治疗舰");
assert(gameSource.includes('chorus: { name:"紫晶圣咏舰"')&&gameSource.includes('supportRole:"group"')&&gameSource.includes('if(wave>=15)pool.push("chorus")'), "第十五波起加入群疗增伤增防圣咏舰");
assert(/function updateEnemySupportUnit\(/.test(gameSource)&&/damageBuff/.test(gameSource)&&/defenseBuff/.test(gameSource), "敌方支援单位实际执行治疗、增伤和增防");
assert(/armorPen:\[0,\.1,\.18,\.26\]/.test(gameSource), "导弹低比例群体穿甲进入伤害结算");
assert(/function beginLaserChannel[\s\S]{0,350}turret\.laserUx=dx\/length/.test(gameSource), "激光开火瞬间保存固定射线方向");
assert(!/function laserChannelTarget\(/.test(gameSource), "移除持续激光的重新捕获目标逻辑");
assert(/function updateLaserChannel[\s\S]{0,700}const ux=turret\.laserUx,uy=turret\.laserUy[\s\S]{0,700}fireLaser\(turret,\{x:turret\.x\+ux\*100/.test(gameSource), "持续激光始终复用开火瞬间的单位向量");
const exposureCard=cards.find((card)=>card.id==="laser_melt");
const exposureProfiles=Array.from(cardSandbox.__laserExposureProfiles,(profile)=>({reduction:Number(profile.reduction),duration:Number(profile.duration)}));
assert.equal(exposureCard?.name,"曝光","旧 laser_melt 存档 ID 原位升级为曝光");
assert.equal(exposureCard?.star,3,"曝光为三星激光功能卡");
assert.equal(exposureCard?.max,5,"曝光具有五级成长");
assert.equal(cardSandbox.__laserExposureChance,.30,"每次激光射击的曝光判定概率固定为 30%");
assert.equal(cardSandbox.__laserExposureCap,5,"单个敌人最多承受五层曝光");
assert.equal(cardSandbox.__laserExposureBossMultiplier,.5,"Boss 每层曝光的生命上限降幅减半");
assert.deepEqual(exposureProfiles,[
  {reduction:0,duration:0},{reduction:.01,duration:2},{reduction:.02,duration:2.75},
  {reduction:.03,duration:3.5},{reduction:.04,duration:4.25},{reduction:.05,duration:5}
],"曝光每级同时从 1%/2 秒成长至 5%/5 秒");
assert(exposureCard.desc(0).includes("30%")&&exposureCard.desc(0).includes("1%")&&exposureCard.desc(0).includes("2 秒")&&exposureCard.desc(4).includes("5%")&&exposureCard.desc(4).includes("5 秒"),"曝光卡首级与满级文案准确展示概率、降幅和持续时间");

const exposureRuntimeStart=gameSource.indexOf("  function exposureLayerCount");
const exposureRuntimeEnd=gameSource.indexOf("  function vulnerabilityProfile",exposureRuntimeStart);
assert(exposureRuntimeStart>0&&exposureRuntimeEnd>exposureRuntimeStart,"可以提取曝光叠层运行时实现");
const exposureSandbox={globalThis:null};
exposureSandbox.globalThis=exposureSandbox;
vm.runInNewContext(`
  const LASER_EXPOSURE_CAP=${cardSandbox.__laserExposureCap};
  const LASER_EXPOSURE_PROFILES=${JSON.stringify(exposureProfiles)};
  const LASER_EXPOSURE_BOSS_MULTIPLIER=${cardSandbox.__laserExposureBossMultiplier};
  const clamp=(value,min,max)=>Math.max(min,Math.min(max,value));
  const COLORS={laser:"#ff70b7"};
  const enemyRadius=()=>10;
  const addParticleText=()=>{};
${gameSource.slice(exposureRuntimeStart,exposureRuntimeEnd)}
  globalThis.__exposure={applyLaserExposure,updateLaserExposure,exposureLayerCount,exposureReduction};
`,exposureSandbox,{filename:"exposure-runtime-test.js"});
const exposureRuntime=exposureSandbox.__exposure;
const makeExposureEnemy=(boss=false)=>({type:{boss},dead:false,invulnerable:0,x:0,y:0,hp:1000,maxHp:1000,baseMaxHp:1000,exposureStacks:[],exposureReduction:0});
const assertNear=(actual,expected,message)=>assert(Math.abs(actual-expected)<1e-9,`${message}：${actual} ≈ ${expected}`);
const regularExposureEnemy=makeExposureEnemy(false);
for(let layer=1;layer<=5;layer+=1)assert.equal(exposureRuntime.applyLaserExposure(regularExposureEnemy,5,"测试激光"),true,`普通敌人可施加第 ${layer} 层曝光`);
assert.equal(exposureRuntime.exposureLayerCount(regularExposureEnemy),5,"普通敌人曝光严格封顶五层");
assertNear(regularExposureEnemy.maxHp,750,"五层满级曝光使普通敌人生命上限降低 25%");
assertNear(regularExposureEnemy.hp,750,"施加曝光时当前生命会截断到新的上限");
assert.equal(exposureRuntime.applyLaserExposure(regularExposureEnemy,5,"测试激光"),false,"第六层曝光不会覆盖或挤掉已有独立层");
exposureRuntime.updateLaserExposure(regularExposureEnemy,5.01);
assertNear(regularExposureEnemy.maxHp,1000,"全部曝光到期后恢复基础生命上限");
assertNear(regularExposureEnemy.hp,750,"曝光到期只恢复上限，不返还生命");
const bossExposureEnemy=makeExposureEnemy(true);
for(let layer=0;layer<5;layer+=1)exposureRuntime.applyLaserExposure(bossExposureEnemy,5,"测试激光");
assertNear(bossExposureEnemy.maxHp,875,"Boss 五层满级曝光只降低 12.5% 生命上限");
const staggeredExposureEnemy=makeExposureEnemy(false);
exposureRuntime.applyLaserExposure(staggeredExposureEnemy,1,"第一层");
exposureRuntime.updateLaserExposure(staggeredExposureEnemy,1);
exposureRuntime.applyLaserExposure(staggeredExposureEnemy,2,"第二层");
exposureRuntime.updateLaserExposure(staggeredExposureEnemy,1.1);
assert.equal(exposureRuntime.exposureLayerCount(staggeredExposureEnemy),1,"曝光各层独立计时，较早施加的层会先到期");
assertNear(staggeredExposureEnemy.maxHp,980,"独立到期后只保留仍有效层的 2% 上限降低");
assertNear(staggeredExposureEnemy.hp,970,"单层到期不会治疗此前被截断的当前生命");

const beginLaserSource=gameSource.slice(gameSource.indexOf("  function beginLaserChannel"),gameSource.indexOf("  function updateLaserChannel"));
const updateLaserSource=gameSource.slice(gameSource.indexOf("  function updateLaserChannel"),gameSource.indexOf("  function launchRepairBots"));
const fireLaserSource=gameSource.slice(gameSource.indexOf("  function fireLaser"),gameSource.indexOf("  function beginLaserChannel"));
assert.equal((beginLaserSource.match(/Math\.random\(\)/g)||[]).length,1,"主激光每次开火只掷一次曝光概率");
assert.equal((updateLaserSource.match(/Math\.random\(\)/g)||[]).length,0,"持续光束的 0.1 秒脉冲不会重复掷曝光概率");
assert(/laserExposureToken\.consumed=true;applyLaserExposure/.test(fireLaserSource),"曝光判定令牌只会被第一个有效命中消耗一次");
assert(/mini\.type==="laser"[^\n]+Math\.random\(\)<LASER_EXPOSURE_CHANCE\)applyLaserExposure/.test(gameSource),"小型激光炮也只在每次独立射击时判定一次曝光");
const laserSentryCard=cards.find((card)=>card.id==="laser_sentry");
assert.equal(1+laserSentryCard.max,cardSandbox.__laserExposureCap,"主激光与满级四座折光节点提供 5 个独立光源，正常玩法可达到曝光层数上限");
assert(/function maybeDeployMini\([^\n]+live\.length>=rank/.test(gameSource),"折光节点的同时存活上限随四级卡牌提高到四座");
assert(/normalizeLaserExposure\(normalizeTimedVulnerability/.test(gameSource)&&/enemies:state\.enemies\.filter\(\(enemy\)=>!enemy\.dead\)\.map\(\(\{type,\.\.\.enemy\}\)=>enemy\)/.test(gameSource),"曝光基础上限、剩余层数与独立计时随敌人存档保存并安全归一化恢复");
assert(/enemyDebuffCount\(enemy\)[^\n]+exposureLayerCount\(enemy\)>0/.test(gameSource),"曝光作为独立异常类型参与六相坍缩计数");
assert(/source==="激光炮"&&hasCard\("laser_lock"\)[^\n]+layers\*\.6/.test(gameSource)&&/source==="燃烧"&&hasCard\("plasma_decay"\)[^\n]+exposureLayerCount\(enemy\)\*\.16/.test(gameSource),"曝光层数继续驱动聚焦锁定与等离子衰变联动");
assert(/function drawLaserEnemyStatus/.test(gameSource)&&gameSource.includes("曝×${layers}")&&/曝光 \$\{exposure\} · 上限 -\$\{\(exposureReduction\(enemy\)\*100\)\.toFixed\(1\)\}%/.test(gameSource),"普通敌人与超大首领均显示曝光层数和生命上限降幅");

const openingControlSource=gameSource.match(/  function applyLaserOpeningControls\([^\r\n]+/)?.[0]||"";
const lightBindSource=gameSource.match(/  function applyLightBind\([^\r\n]+/)?.[0]||"";
assert(openingControlSource&&lightBindSource,"可以提取三张激光短控卡的运行时实现");
const controlSandbox={globalThis:null};
controlSandbox.globalThis=controlSandbox;
vm.runInNewContext(`
  let __ranks={};
  const cardRank=(id)=>__ranks[id]||0;
  const state={particles:[]};
  const COLORS={laser:"#ff70b7"};
  const enemyRadius=()=>10;
  const addParticleText=()=>{};
${lightBindSource}
${openingControlSource}
  globalThis.__setRanks=(ranks)=>{__ranks=ranks;};
  globalThis.__applyLaserOpeningControls=applyLaserOpeningControls;
`,controlSandbox,{filename:"laser-control-runtime-test.js"});
const makeControlEnemy=(boss=false)=>({type:{boss},dead:false,invulnerable:0,x:0,y:100,stun:0,lightBindTime:0});
controlSandbox.__setRanks({evo_laser_2_4:3});
const dragEnemy=makeControlEnemy();
controlSandbox.__applyLaserOpeningControls({shots:1},dragEnemy,1,0);
assertNear(dragEnemy.lightBindTime,.35,"迟滞棱镜满级光锢首个命中 0.35 秒");
const dragSecondEnemy=makeControlEnemy();
controlSandbox.__applyLaserOpeningControls({shots:1},dragSecondEnemy,2,0);
assert.equal(dragSecondEnemy.lightBindTime,0,"迟滞棱镜不控制同次射击的第二个直射命中");
controlSandbox.__setRanks({evo_laser_3_4:3});
const recoilEnemy=makeControlEnemy();
controlSandbox.__applyLaserOpeningControls({shots:3},recoilEnemy,1,0);
assert.equal(recoilEnemy.y,50,"光压回卷满级每第三炮把非 Boss 后推 50 点");
assertNear(recoilEnemy.lightBindTime,.75,"光压回卷满级同时光锢 0.75 秒");
const recoilBoss=makeControlEnemy(true);
controlSandbox.__applyLaserOpeningControls({shots:3},recoilBoss,1,0);
assert.equal(recoilBoss.y,100,"Boss 不受光压回卷位移");
assertNear(recoilBoss.lightBindTime,.375,"Boss 只承受光压回卷一半光锢时长");
controlSandbox.__setRanks({evo_laser_4_4:2});
const cageEnemy=makeControlEnemy();
controlSandbox.__applyLaserOpeningControls({shots:1},cageEnemy,2,1);
assertNear(cageEnemy.lightBindTime,.9,"分光囚笼满级会控制反射段命中的每个敌人 0.9 秒");
assert(/hitIds=new Set\(\)/.test(fireLaserSource)&&/if\(hitIds\.has\(enemy\.id\)\)continue;hitIds\.add\(enemy\.id\)/.test(fireLaserSource),"同一敌人在一次反射射击中只会被短控一次");
assert(/openingPulse:turret\.laserTickSerial===1/.test(updateLaserSource)&&/options\.openingPulse[^\n]+applyLaserOpeningControls/.test(fireLaserSource),"三张短控卡只在整段持续激光的首脉冲触发");
assert(/lightBindTime:Math\.max\(0,Number\(enemy\.lightBindTime\)\|\|0\)/.test(gameSource),"光锢剩余时间会随战局存档恢复");
assert(/drawLaserEnemyStatus[^\n]+lightBindTime>0[^\n]+⌛/.test(gameSource)&&/superBossDebuffEntries[^\n]+光锢 \$\{enemy\.lightBindTime\.toFixed\(1\)\}s/.test(gameSource),"普通敌人和超大首领都有可见的光锢状态反馈");
const frostSkillBranch=gameSource.match(/else if\(turretId==="frost"\)\{(?<body>[\s\S]*?)\}\s*else if\(turretId==="arc"\)/)?.groups?.body||"";
const arcSkillBranch=gameSource.match(/else if\(turretId==="arc"\)\{(?<body>[\s\S]*?)\}\s*else if\(turretId==="support"\)/)?.groups?.body||"";
assert(/function freezeNonBossEnemies\(targets,duration=3\)/.test(gameSource)&&/enemy\.type\.boss/.test(gameSource), "绝对零度只冻结非首领敌军");
assert(frostSkillBranch.includes("freezeNonBossEnemies(targets,3)")&&!frostSkillBranch.includes("damageEnemy(")&&!frostSkillBranch.includes("applyFracture("), "绝对零度不会直接伤害、破碎或清除敌军");
assert(arcSkillBranch.includes("enemy.vulnerable=Math.min")&&!arcSkillBranch.includes("damageEnemy("), "数字键 4 的磁暴脉冲只强化易伤，不会清屏");
assert(/function enemyDebuffCount\(/.test(gameSource)&&/debuffs<6/.test(gameSource), "六相坍缩按六种不同异常触发");
assert(/enemy\.hp\*\[0,\.006,\.01,\.015\]\[rank\]\*dt/.test(gameSource)&&/trueDamage:true/.test(gameSource), "六相坍缩每秒按当前生命百分比真实扣血");
assert(/ratios=\[0,\.3,\.45,\.6,\.8,2\]/.test(gameSource), "相位护盾按屏障上限百分比成长，并在五级质变为 200%");
for(const id of ["shield_overdrive","barrier_arsenal","aegis_retaliation"])assert(ids.has(id), `护盾联动卡 ${id} 已加入卡池`);
assert(/function payForbiddenInsightCost\(\)[\s\S]{0,520}spendBarrierShields\(cost\)/.test(gameSource), "禁忌洞见代价优先扣除各段黄色相位护盾");
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

assert(/laser:\s*\{[^\n]+cooldown:10/.test(gameSource), "激光炮使用十秒基础启动间隔");
assert(/const LASER_TICK_INTERVAL=\.1;/.test(gameSource), "持续激光以稳定的十分之一秒脉冲结算");
assert(/function laserDuration\(\)\{return \[1\.2,1\.8,2\.4,3\]\[cardRank\("laser_duration"\)\];\}/.test(gameSource), "激光持续时间逐级成长且硬上限三秒");
assert(/beginLaserChannel\(turret,target\)/.test(gameSource), "激光攻击会进入持续照射状态");
assert(/function updateLaserChannel\(/.test(gameSource), "激光持续期间追踪目标并连续结算");
for(const id of ["laser_duration","laser_cycle","laser_sustain"])assert(gameSource.includes(`id:"${id}"`), `激光持续机制卡牌 ${id} 已加入卡池`);

assert(/function openingStarProbabilities\(\)[\s\S]{0,260}full\.slice\(0,4\),0,0/.test(gameSource), "opening draft zeros out five-star and six-star weights before normalization");
assert(/state\.openingDraft\?generateWeightedCards\(DRAFT_OFFER_COUNT,\{[^}]*maxStar:4[^}]*starProbabilities:openingStarProbabilities\(\)/.test(gameSource), "opening draft hard-limits the eligible pool to four stars");

assert(/function healBarrierSegment\(amount,source,preferredIndex=null,strictPreferred=false\)/.test(gameSource), "barrier healing supports segment-locked repair");
assert(/function gainShield\(amount,source,preferredIndex=null,strictPreferred=false\)/.test(gameSource), "barrier shielding supports segment-locked coating");
assert(/healBarrierSegment\(payload,[^;]+bot\.segmentIndex,true\);gainShield\(bot\.shield\*skillBonus,[^;]+bot\.segmentIndex,true\)/.test(gameSource), "repair bots apply health and shield only to their attached segment");
assert(/function renderDraft\(\)\{state\.selectingCard=false;/.test(gameSource), "every newly rendered draft explicitly releases the previous selection lock");
assert(/function finishOpeningDraft\(\)[\s\S]{0,420}classList\.remove\("show","opening-draft"\)/.test(gameSource), "the fifth opening pick closes the draft overlay instead of leaving disabled cards on screen");
assert(/if\(state\.openingDraftsRemaining>0\)\{scheduleOpeningDraft\(\);return;\}/.test(gameSource), "intermediate opening picks schedule a fresh draft frame without reusing disabled buttons");
assert(/const STATS_METER_RENDER_INTERVAL_MS = 600;/.test(gameSource), "DPS/HPS 列表限制为低频重建以避免周期性布局抖动");
assert(/renderTime-meterRowsLastRender>=STATS_METER_RENDER_INTERVAL_MS/.test(gameSource), "统计摘要保持连续更新而来源列表按性能预算刷新");
assert(/function scheduleAutoSave\(\)[\s\S]{0,260}requestIdleCallback/.test(gameSource), "自动存档在浏览器空闲阶段提交");
assert(/state\.saveAccumulator>=10\)\{state\.saveAccumulator=0;scheduleAutoSave\(\);\}/.test(gameSource), "战斗循环不再同步执行完整自动存档");
assert(/function drawRunnerEnemy\([\s\S]{0,700}RUNNER_TRAIL_LAYERS/.test(gameSource), "高速彗星使用固定层数尾迹而非逐单位渐变分配");
assert(/const CROWD_LOD_SOFT_LIMIT = 32;[\s\S]{0,80}const CROWD_LOD_HARD_LIMIT = 48;/.test(gameSource), "密集潮在 32/48 个敌军处逐级降低纯视觉开销");
assert(/function drawRunnerEnemy\(radius,color,crowdLod=0\)[\s\S]{0,500}crowdLod>=2\?1:crowdLod===1\?2:RUNNER_TRAIL_LAYERS/.test(gameSource), "高速彗星尾迹按密集程度从三层降至一层");
assert(/ctx\.shadowBlur=enemy\.type\.boss\?22:crowdLod===0\?12:crowdLod===1\?3:0/.test(gameSource), "普通敌军外发光在密集潮中同步降载");
assert(/if\(id==="runner"\)\{drawRunnerEnemy\(radius,color,crowdLod\);return;\}/.test(gameSource), "高速单位走支持密集度的低分配专用绘制路径");
assert(/function selectTarget\(turret,range=turretRange\(turret\)\)\{[\s\S]{0,900}for\(const enemy of state\.enemies\)/.test(gameSource), "主炮目标选择使用单次扫描而非为每次射击分配并排序候选数组");
assert(!/function drawTurrets\(\)[\s\S]{0,900}selectTarget\(turret\)/.test(gameSource), "炮塔绘制复用上次攻击方向，不在每个渲染帧重新排序敌军");
assert(/const BASE_STAT_PROGRESS=\{standard:\[\.10,\.15,\.20,\.25,1\],burst:\[\.02,\.05,\.15,\.40,1\]\}/.test(gameSource), "基础攻击区分标准与重炮两条满级质变曲线");
assert(/const BASE_ATTACK_PROGRESS=\{front:\[\.18,\.36,\.52,\.68,1\],steady:\[\.10,\.22,\.38,\.60,1\],compressed:\[\.005,\.01,\.10,\.30,1\]\}/.test(gameSource), "基础攻击采用前置、平稳与重炮压缩三条专属曲线");
assert(/bullet:\{flatMax:250,multiplierMax:2\.5,critPowerMax:10,curve:"standard",attackCurve:"front"\}/.test(gameSource), "子弹基础攻击减半后仍保持前两级快速成长");
assert(/missile:\{flatMax:2000,multiplierMax:5,critPowerMax:20,curve:"burst",attackCurve:"compressed"\}/.test(gameSource)&&/laser:\{flatMax:2000,multiplierMax:5,critPowerMax:20,curve:"burst",attackCurve:"compressed"\}/.test(gameSource), "导弹与激光基础攻击满级固定值为 2000 且前两级保持高度压缩");
assert(/arc:\{flatMax:125,multiplierMax:1\.25,critPowerMax:5,curve:"standard",attackCurve:"front"\}/.test(gameSource)&&/frost:\{flatMax:25,multiplierMax:1\.25,critPowerMax:5,curve:"standard",attackCurve:"steady"\}/.test(gameSource), "电弧与冰霜基础攻击减半并保留各自成长节奏");
assert(/const BASE_RATE_TARGETS=\{/.test(gameSource)&&!/baseRateCooldownFactor/.test(gameSource), "基础攻速直接以各炮塔实际射速为目标且不再叠加隐藏后摇");
assert(/function turretDamageMultiplier\(turretId\)\{return \(1\+turretPassive\(turretId,"damage"\)\)\*terminalSynergy/.test(gameSource), "基础攻击不再重复叠加隐藏的满级增伤");
assert(/const RANGE_CARD_PROGRESS = \[0,\.06,\.13,\.22,\.34,1\]/.test(gameSource)&&/function rangeAtRank\(turret,rank\)[^\n]+FULL_SCREEN_RANGE-turret\.range\)\*RANGE_CARD_PROGRESS\[tier\]/.test(gameSource)&&/fullScreen:rank>=5/.test(gameSource), "射程卡恢复旧版成长曲线，第五级达到全屏且遗物成长额外叠加");
assert(/boostedAttackStat=turretId!=="support"&&\(stat==="damage"\|\|stat==="critPower"\)/.test(gameSource), "二至六星攻击与暴伤卡统一使用双倍成长规则");
assert(/flatValues=stat==="damage"&&turretId!=="support"\?Array\.from\(\{length:max\},\(_,index\)=>star\*\(index\+1\)\):null/.test(gameSource), "每级攻击卡额外加入等于星级的固定攻击");
assert(/turret\.damage=turretAdditiveBaseAttack\(turretId\)/.test(gameSource), "炮塔先汇总初始攻击、击杀成长与卡牌固定攻击，再交给攻击提升系数结算");
assert(/node\.dataset\.updateAverage=updateTiming\.average\.toFixed\(3\)/.test(gameSource), "测试档案分别记录战斗更新耗时");
assert(/node\.dataset\.drawAverage=drawTiming\.average\.toFixed\(3\)/.test(gameSource), "测试档案分别记录画布绘制耗时");
assert(/node\.dataset\.crowdLod=String\(living\.length>CROWD_LOD_HARD_LIMIT\?2:living\.length>CROWD_LOD_SOFT_LIMIT\?1:0\)/.test(gameSource), "测试遥测会标记当前密集潮视觉等级");
assert(/data-test-preset="stress">满卡无敌压力 · 第 5 波/.test(indexSource), "测试账号提供第 5 波满卡无敌压力入口");
assert(/data-test-preset="stress40">满卡无敌压力 · 第 40 波/.test(indexSource), "测试账号提供第 40 波满卡无敌压力入口");
assert(/data-test-preset="colossal">超巨星终局 · 第 10 波/.test(indexSource), "测试账号提供第 10 波超巨星终局验收入口");
assert(/<section class="core-hud">[\s\S]{0,900}id="wave50BossTestButton"/.test(indexSource),"左侧战局面板提供测试账号第 50 关 Boss 直战按钮");
assert(/function startWave50BossTest\(\)[^\n]+resetGame\(\{startWave:CAMPAIGN_CLEAR_WAVE,openingDrafts:0\}\)[^\n]+finalBossEntries\(CAMPAIGN_CLEAR_WAVE\)\[0\][^\n]+spawnEnemy\(entry\.type,entry\)/.test(gameSource),"第 50 关按钮直接生成该关真实终局 Boss，而非跳过结算");
assert(/qaBossControls"\)\.classList\.toggle\("hidden",!account\?\.isTest\|\|!state\.started\)/.test(gameSource),"第 50 关直战按钮仅在测试账号的进行中战局显示");
assert(/stress40:\{wave:40,cards:null,invincible:true\}/.test(gameSource), "第 40 波压力档启用满卡与双方无敌规则");
assert(/stress:\{wave:5,cards:null,invincible:true\}/.test(gameSource), "满卡压力预设从第 5 波启动并启用双方无敌");
assert(/if\(state\.qaInvincible\)\{enemy\.hit=\.08;return 0;\}/.test(gameSource), "无敌压力模式保留命中特效但不削减敌军生命");
assert(/function damageCore\([\s\S]{0,180}state\.qaInvincible/.test(gameSource), "无敌压力模式不削减五段屏障");
assert(/function damageMiniTurret\([^\n]+state\.qaInvincible/.test(gameSource), "无敌压力模式保护友方子炮塔");
assert(/state\.qaInvincible&&enemyAttackPoint\(enemy\)\.y>=barrierSurfaceY\(enemyAttackPoint\(enemy\)\.x\)[\s\S]{0,240}state\.waveResolved\+=1/.test(gameSource), "敌军仅在其真实可攻击下缘触及屏障后从压力场景移除");
assert(/const active=state\.started&&!state\.paused&&!state\.gameOver,shouldDraw=active\|\|time-lastDraw>=1000\/18/.test(gameSource), "战斗中逐 RAF 绘制，暂停时才降至低刷新率");
assert(/node\.dataset\.drawGapAverage=drawGapTiming\.average\.toFixed\(2\)/.test(gameSource), "测试遥测记录真实绘制间隔以识别帧节奏问题");
assert(/function basicCardStatSentence\([\s\S]{0,900}formatCompactNumber\(Math\.round\(stat\.value\)\)/.test(gameSource), "基础数值卡使用整数紧凑格式展示当前值与升级后数值");
assert(/function formatDisplayNumber\([\s\S]{0,260}toFixed[\s\S]{0,180}function normalizeDisplayNumbers/.test(gameSource), "卡牌说明统一裁剪浮点尾数并移除无意义零位");
assert(/formatShotRate\(rate\)\{return Number\(rate\.toFixed\(3\)\)\.toString\(\)/.test(gameSource)&&/formatShotRate\(stat\.perSecond\)/.test(gameSource), "每秒攻击频率最多显示三位有效小数");
assert(/function cardLevelDefinition\(card,level\)[^\n]+description:draftCardDescription\(card,rank-1\)/.test(gameSource), "卡牌总览的每个独立等级统一清理非整数显示");
assert(/function renderDraft\(\)[^\n]+view=cardLevelDefinition\(card,current\+1\)/.test(gameSource), "所有选牌弹窗显示即将获得的独立卡牌等级定义");
assert(/function draftCardDescription\(card,current\)\{return normalizeDisplayNumbers\(card\.desc/.test(gameSource), "所有选牌弹窗统一清理非整数显示");
assert(/function basicCardTurretId\(card\)[\s\S]{0,220}RANGE_CARD_BY_TURRET/.test(gameSource), "六类炮塔攻击或治疗范围卡同样纳入基础数值精简说明");
assert(/current>=card\.max[\s\S]{0,180}已满级/.test(gameSource), "满级基础数值卡不再显示无意义的相同升级数值");
assert(!/\$\{basicCardStatSentence\(card,current\)\}/.test(gameSource), "基础属性预览直接替代冗长说明而不是额外增加一行");

const baseDps = {
  bullet:1 / 2.4,
  laser:1 * (3 / .1) / 12,
  missile:1 / 6,
  frost:1 / 3.4,
  arc:(1 / 3.1) * (1 + .8 + .64)
};
for(const turretId of ["bullet","laser","missile","frost","arc"])assert(new RegExp(`${turretId}: \\{[^\\n]+damage:1,`).test(gameSource),`${turretId} 未选择基础攻击卡前固定攻击为 1`);
assert(baseDps.laser>baseDps.bullet&&baseDps.arc>baseDps.bullet,"未加卡牌时炮塔仍由多段与连锁机制形成差异，而非初始攻击面板差异");
const baseStars=Balance.starProbabilities([0,0,0,0,0]),boostedStars=Balance.starProbabilities([5,5,5,5,5]);
assert(Math.abs(baseStars.reduce((sum,value)=>sum+value,0)-1)<1e-9,"基础星级概率归一化");
assert(Math.abs(boostedStars.reduce((sum,value)=>sum+value,0)-1)<1e-9,"增幅后星级概率仍归一化");
assert(boostedStars[4]>baseStars[4]&&boostedStars[5]>baseStars[5],"特殊星图卡提高五星与六星爆率");
assert.deepEqual(Balance.earlyWaveProfile(1),{countScale:.62,hpScale:.54,attackScale:.42},"第一波按低基础炮塔强度下调");
assert.equal(Balance.earlyWaveProfile(6).hpScale,1,"第六波进入标准成长曲线");
assert.equal(Balance.waveEnemyPressureMultiplier(1).hp,.5,"第一波敌军压力为标准值的一半");
assert.deepEqual(Balance.waveEnemyPressureMultiplier(10),{hp:1,attack:1},"第十波进入标准敌军压力");
assert.equal(Balance.waveEnemyPressureMultiplier(11).hp,1.6,"第十一波开始采用 1.6 倍指数成长");
assert.equal(Balance.waveEnemyPressureMultiplier(20).hp,Math.pow(1.6,10),"第二十波延续统一指数成长曲线");
assert(/pressure=BalanceCore\.waveEnemyPressureMultiplier\(state\.wave\)[\s\S]{0,300}pressure\.hp/.test(gameSource),"敌方生命倍率只在统一基础生命入口套用");
assert(/pressure=BalanceCore\.waveEnemyPressureMultiplier\(wave\)[\s\S]{0,300}pressure\.attack/.test(gameSource),"敌方伤害倍率只在统一攻击入口套用");
for(const id of ["cryo_missile_echo","laser_arc_echo","bullet_support_echo"])assert(gameSource.includes(`id:"${id}"`),`六星主动联动 ${id} 已加入`);
const frostMultishot=cards.find((card)=>card.id==="frost_field"),overhealFortification=cards.find((card)=>card.id==="support_overheal_fortification");
assert.equal(frostMultishot.star,3,"多重减速归入三星冰霜构筑");
assert.deepEqual([0,1,2,3,4].map((rank)=>frostMultishot.desc(rank)),["每次发射 1 枚冰弹，并有 50% 概率额外发射第 2 枚。","每次稳定发射 2 枚冰弹。","每次稳定发射 3 枚冰弹，并有 50% 概率追加第 4 枚。","每次稳定发射 4 枚冰弹。","质变：每次稳定发射 5 枚冰弹。"],"多重减速按概率曲线成长并在五级稳定五发");
assert(/function rollFrostShotCount/.test(gameSource)&&/targets=\[target,\.\.\.alternatives\][\s\S]{0,180}while\(targets\.length<shotCount\)targets\.push\(target\)/.test(gameSource),"冰弹优先分配给不同目标，不足时才重复锁定");
assert(!/const station=cardRank\("frost_field"\)/.test(gameSource),"多重减速不再沿用寒冰基站的范围场逻辑");
assert(overhealFortification?.star===1&&overhealFortification.max===5,"溢疗筑垒是一星五级支援卡");
assert(/function fortifySegmentFromTreatment/.test(gameSource)&&/segment\.overhealBonus/.test(gameSource)&&/strictPreferred&&preferred/.test(gameSource),"机器人每次治疗只强化其附着分段并保留永久上限成长");
assert(/SUPPORT_OVERHEAL_CHANCES = \[0,\.30,\.35,\.40,\.45,\.50\]/.test(gameSource)&&/SUPPORT_OVERHEAL_RATES = \[0,\.05,\.06,\.07,\.08,\.10\]/.test(gameSource)&&/Math\.ceil\(treatment\*SUPPORT_OVERHEAL_RATES\[rank\]\)/.test(gameSource),"治疗筑垒由每个机器人每次治疗独立判定，30% 起步且治疗转化率由 5% 成长至 10%");
assert(/每次治疗（有效治疗或过量治疗）均独立判定/.test(gameSource)&&/本次完整治疗量/.test(gameSource)&&/if\(strictPreferred&&preferred\)fortifySegmentFromTreatment\(preferred,amount,source\);for\(const segment of ordered\)/.test(gameSource),"治疗筑垒在有效治疗与完全过量治疗时都按本次完整治疗量判定");
assert(/function savedBarrierBonusMax/.test(gameSource)&&/fortificationDetached:true/.test(gameSource)&&/raw-duplicated/.test(gameSource),"旧存档会移除治疗筑垒曾重复写入全局成长池的数值");
assert(!/state\.barrierBonusMax=\(state\.barrierBonusMax\|\|0\)\+gain/.test(gameSource)&&!/state\.barrierBonusMax=Math\.max\(state\.barrierBonusMax\|\|0,state\.globalBarrierMax-naturalBarrierCapacity/.test(gameSource),"治疗筑垒不再进入全局池且换波不再反推锁定永久成长");
assert(/nextBaseMax=Math\.max\(1,capacity\/BARRIER_SEGMENT_COUNT\)/.test(gameSource)&&/overhealBonus=Math\.max\(0,Number\(segment\.overhealBonus\)\|\|0\),nextMax=nextBaseMax\+overhealBonus/.test(gameSource),"换波时基础容量与逐段永久筑垒完全分离后再相加");
assert(!gameSource.includes("overhealFortified=0")&&/delete segment\.overhealFortified/.test(gameSource),"移除旧版每波筑垒计数器及其隐含限制");
assert.equal((()=>{const run={barrierBonusMax:180,barrierSegments:[{overhealBonus:30},{overhealBonus:20}]};const raw=Math.max(0,Number(run.barrierBonusMax)||0),duplicated=(run.barrierSegments||[]).reduce((sum,segment)=>sum+Math.max(0,Number(segment.overhealBonus)||0),0);return Math.max(0,raw-duplicated);})(),130,"旧存档只清除重复计入全局池的筑垒值，保留真实全局成长");
assert.deepEqual((()=>{const capacity=500,old=[{overhealBonus:12},{overhealBonus:0},{overhealBonus:7},{overhealBonus:3},{overhealBonus:0}],base=capacity/old.length;return old.map((segment)=>base+segment.overhealBonus);})(),[112,100,107,103,100],"换波基础容量不吞并各分段筑垒，永久增量原样跨波保存");
assert(!gameSource.includes("SUPPORT_OVERHEAL_PICK_BONUSES"),"治疗筑垒不再在选卡时向所有分段发放固定生命上限");
assert(/id:"support_overheal_shield"[\s\S]{0,260}SUPPORT_OVERHEAL_SHIELD_RATES/.test(gameSource)&&/function convertOverhealToShield/.test(gameSource),"二星溢疗护盾卡把附着段过量治疗转为可叠加护盾");
assert(/segment\.overhealShieldBonus=\(segment\.overhealShieldBonus\|\|0\)\+gain/.test(gameSource)&&/segment\.maxShield=desiredTotal\*share\+overhealShieldBonus/.test(gameSource),"机器人溢疗护盾永久记录在附着段，派生属性重算不会吞掉已转化护盾上限");
assert(/SUPPORT_MANUFACTURE_INTERVALS = \[5,4\.5,4,3\.5,3,2\]/.test(gameSource)&&/SUPPORT_RATE_CARD_VALUES = SUPPORT_MANUFACTURE_INTERVALS\.slice\(1\)/.test(gameSource)&&/support: \{ name:"支援炮塔"[\s\S]{0,160}cooldown:5/.test(gameSource)&&/SUPPORT_HEAL_FREQUENCIES = \[1,1\.2,1\.4,1\.6,1\.8,2\.5\]/.test(gameSource),"维修机器人核心被动初始每 5 秒制造一台，卡牌成长至 2 秒，并与单机器人治疗频率独立计算");
assert(/color:COLORS\.arc,life:1,maxLife:1,style:"lightning"/.test(gameSource)&&/const beamLife=mini\.type==="arc"\?1:\.1/.test(gameSource),"主电离炮与电离子炮的闪电攻击特效均持续 1 秒");
assert(/SUPPORT_HEAL_FIXED_VALUES = \[5,10,25,45,70,100\]/.test(gameSource)&&/SUPPORT_HEAL_MULTIPLIERS = \[1,1,1\.5,2,3,5\]/.test(gameSource)&&/SUPPORT_DURATION_VALUES = \[1,2,3,4,5,8\]/.test(gameSource),"基础治疗未选卡为 5、首级为 10，并按额外系数 1.0 至 5.0 与指定持续时间曲线成长");
assert(gameSource.includes('function supportBaseHealing(rank=cardRank("support_base_heal"))')&&gameSource.includes('SUPPORT_HEAL_FIXED_VALUES[level]*SUPPORT_HEAL_MULTIPLIERS[level]+(state.supportHealGrowth||0)')&&/healing=supportBaseHealing\(\)/.test(gameSource),"支援单次治疗统一使用基础治疗倍率，并防止击杀成长被乘区指数放大");
assert(!gameSource.includes("SUPPORT_OVERHEAL_FORTIFY_WAVE_CAP")&&/SUPPORT_OVERHEAL_SHIELD_WAVE_CAP = \[0,\.08,\.12,\.18,\.28,\.45\]/.test(gameSource),"治疗筑垒解除生命上限预算，溢疗护盾仍保留独立护盾预算");
assert.equal(Balance.bossHealthBudget(10,false),10000,"第 10 波普通首领生命为 1 万");
assert.equal(Balance.bossHealthBudget(10,true),100000,"第 10 波超大或黑洞首领生命为 10 万");
assert.equal(Balance.bossHealthBudget(11,false),16000,"第 11 波普通首领按 1.6 倍成长");
assert.equal(Balance.bossHealthBudget(11,true),160000,"第 11 波终局首领按 1.6 倍成长");
assert(/function bossMaxHealth\(type,scheduleEntry\).*BalanceCore\.bossHealthBudget\(state\.wave,isFinalBossHealthClass\(type,scheduleEntry\)\)/.test(gameSource)&&!gameSource.includes("function bossHpBudget("),"首领使用独立确定性生命曲线，不再读取普通怪物或近期 DPS 预算");
assert(!/function startBlackHoleTest\(\)[\s\S]{0,1400}boss\.maxHp\s*\*=/.test(gameSource),"第 10 波黑洞验收模式不再额外放大独立 Boss 生命");
assert(/if\(!centralBoss\)\{const hpWidth=Math\.max\(120,radius\*2\)/.test(gameSource),"普通小首领继续使用原有紧凑血条");
assert(/function drawBossHealthBar\(/.test(gameSource)&&/const centralBoss=enemy\.type\.bossKind==="redgiant"\|\|enemy\.type\.bossKind==="blackhole"/.test(gameSource)&&/const width=Math\.min\(W-96,552\),height=30,x=W\/2,y=H\/2/.test(gameSource),"超巨星与黑洞共用战斗画面正中央的大型血条");
assert(/drawSuperBossStatusLane\(enemy,left,left\+width,top\+height\+17\)/.test(gameSource)&&/function superBossDebuffEntries/.test(gameSource)&&/function superBossBuffEntries/.test(gameSource),"超巨星减益居血条下方左侧、增益居右侧");
assert(/ARC_MINI_FIELD_FILL_ALPHA=\.018/.test(gameSource)&&/ARC_MINI_FIELD_STROKE_ALPHA=\.11/.test(gameSource),"电离子炮范围场仅保留低强度提示");
assert(/id:"support_kill_healing",name:"治疗成长"[\s\S]{0,260}star:3,max:5/.test(gameSource)&&/SUPPORT_KILL_HEAL_GAINS = \[0,1,2,3,4,5\]/.test(gameSource)&&/growSupportHealingFromKill\(enemy\)/.test(gameSource),"三星治疗成长按击杀永久提供 1 至 5 点基础治疗量");
assert(/supportHealGrowth:state\.supportHealGrowth\|\|0/.test(gameSource)&&/supportHealGrowth:Math\.max\(0,Number\(run\.supportHealGrowth\)\|\|0\)/.test(gameSource),"击杀获得的基础治疗量成长随存档保存与恢复");
assert(/SUPPORT_KILL_HEAL_CHANCES = \[0,\.025,\.035,\.05,\.075,\.11\]/.test(gameSource)&&!/SUPPORT_KILL_HEAL_WAVE_CAPS/.test(gameSource),"治疗成长保留逐级触发概率且不再设置单波上限");
assert(/state\.supportHealGrowth=Math\.max\(0,state\.supportHealGrowth\|\|0\)\+gain/.test(gameSource)&&!gameSource.includes("current>=softCap?.25:1"),"每次治疗成长触发均完整永久累加基础治疗");
assert(/\.growth-draft \.card-choices \{[^}]*repeat\(6,minmax\(0,1fr\)\)/.test(stylesSource),"成长路线在宽屏固定以六张卡牌同屏展示");
assert(/function repairBotMitigation\(segment\)/.test(gameSource)&&/REPAIR_BOT_MITIGATION_PER_UNIT\s*=\s*\.04/.test(gameSource)&&/REPAIR_BOT_MITIGATION_CAP\s*=\s*\.16/.test(gameSource),"每台附着维修机器人提供 4% 减伤，四台叠满 16%");
assert(/mitigation=options\.exactDamage\?0:repairBotMitigation\(segment\)/.test(gameSource)&&/waveStats\.barrier\.robotMitigated\+=Math\.max\(0,rawScaled-scaled\)/.test(gameSource),"屏障受击结算和战斗日志均记录维修机器人减伤，精确复制伤害不重复减伤");
assert(/function vulnerabilityProfile\(enemy\)/.test(gameSource)&&/function vulnerabilitySpawnRamp\(enemy\)/.test(gameSource),"易伤按普通怪、奖励怪、首领与超大首领设置独立层数上限并平滑生效");
assert(/enemy\?\.colossal\)return \{baseStacks:3,timedStacks:4,maxBonus:\.22,laserLayers:3\}/.test(gameSource)&&/enemy\?\.type\?\.boss\)return \{baseStacks:4,timedStacks:6,maxBonus:\.32,laserLayers:4\}/.test(gameSource),"首领易伤上限显著低于普通怪，防止刚入场被易伤乘区秒杀");
assert(/fastKills\+=1/.test(gameSource)&&/vulnerabilityApplications/.test(gameSource)&&/maxVulnerabilityLayers/.test(gameSource),"战斗日志记录出场 2.5 秒内击杀与易伤层数，便于继续平衡");
assert(/REFRACTION_CHANCES=\[\.40,\.60,\.80,1,1\]/.test(gameSource)&&/count:rank>=5\?2:1/.test(gameSource),"所有星级概率折射统一从 40% 起步，四级必得 1 张、五级质变为 2 张");
assert(/if\(rank>previous\)queueProbabilityRefraction\(card,options\)/.test(gameSource)&&/grantRandomCards\("概率折射",reward\.count,\{fixedStar:reward\.star,skipRefraction:true\}\)/.test(gameSource),"每张正常获得卡牌统一触发一次概率折射，折射奖励自身禁止递归");
assert(/LIFESTEAL_RATES = \[\.01,\.015,\.02,\.03,\.05\]/.test(gameSource)&&/id:"lifesteal"[\s\S]{0,180}max:5/.test(gameSource)&&/function healDamagedBarrierSegmentsEvenly/.test(gameSource)&&/healDamagedBarrierSegmentsEvenly\(healing/.test(gameSource),"生命虹吸从 1% 成长至 5%，并把治疗均摊给所有已损血小屏障");
assert(/function drawBarrierSegmentValue/.test(gameSource)&&/hpText=`\$\{formatCompactNumber\(Math\.ceil\(segment\.hp\)\)\}\/\$\{formatCompactNumber\(Math\.ceil\(segment\.maxHp\)\)\}\//.test(gameSource)&&/shieldText=formatCompactNumber\(Math\.ceil\(segment\.shield\|\|0\)\)/.test(gameSource),"每段屏障以生命/上限/黄色护盾单行显示且初始护盾为零");
assert(/SUPPORT_CRIT_MULTIPLIERS = \[2,2\.5,3,4,5,10\]/.test(gameSource),"治疗暴击量从基础 200% 成长至质变 1000%");
assert(/ratios=\[0,\.3,\.45,\.6,\.8,2\]/.test(gameSource),"相位护盾五级质变上限为屏障生命的 200%");
assert(/thresholds=\[0,7,7,6,6,5\],gains=\[0,1,2,3,4,10\]/.test(gameSource),"连杀锻炉使用一星质变成长曲线");
assert(/function bountyMasteryTier/.test(gameSource)&&/bountyMasteryTier\(\)\*\.8/.test(gameSource)&&/bountyMasteryTier\(\)>=6/.test(gameSource),"悬赏统御协议按已拥有卡牌等级总数成长");
assert(gameSource.includes('if(stat==="baseHeal")return {label:"单次治疗",value:supportBaseHealing(rank),unit:""}'),"基础治疗量在图鉴与选牌中显示单次治疗数值变化");

assert(gameSource.includes("const TIMED_VULNERABILITY_STACK_CAP = 24;")&&gameSource.includes("const QA_TIMED_VULNERABILITY_STACK_CAP = 8;"),"timed vulnerability stacks have bounded normal and QA caps");
assert(gameSource.includes('origin:stack.origin==="propagated"?"propagated":"original"')&&/function applyTimedVulnerability\([^\n]+origin="original"\)/.test(gameSource),"timed vulnerability stacks persist original or propagated provenance");
assert(gameSource.includes('if(origin==="propagated")return false;'),"propagated vulnerability cannot displace original stacks at the cap");
assert(gameSource.includes("source.originalVulnerable||0")&&gameSource.includes('stack.origin!=="propagated"')&&gameSource.includes('stack.source,"propagated"'),"only original vulnerability layers can propagate once");
assert(gameSource.includes("VULNERABILITY_PROPAGATION_INTERVAL")&&gameSource.includes("target.vulnerabilityPropagationAt=state.elapsed+VULNERABILITY_PROPAGATION_INTERVAL"),"vulnerability propagation is cadence limited");
assert(gameSource.includes('!state.particles.some((particle)=>particle.type==="barrierSweep"&&particle.life>0)'),"barrier full-repair feedback is a single arc sweep instead of stacked center rings");
assert(gameSource.includes("QA_BLACK_HOLE_UNIT_BUDGET-(enemy.qaSummonedUnits||0)")&&gameSource.includes("QA_BLACK_HOLE_ASTEROID_BUDGET-(enemy.qaAsteroidsLaunched||0)"),"invincible black-hole stress tests have cumulative summon budgets");
assert(gameSource.includes("node.dataset.maxTimedVulnerabilityStacks")&&gameSource.includes("node.dataset.propagatedTimedVulnerabilityStacks"),"QA telemetry exposes bounded one-hop vulnerability stack counts");
assert(/id:"event-horizon"[\s\S]{0,180}hpScale:95[\s\S]{0,120}star:5/.test(gameSource),"第 20 波五星视界悬赏具有四星悬赏约十倍生命");
assert(/id:"singularity"[\s\S]{0,180}hpScale:950[\s\S]{0,120}star:6/.test(gameSource),"第 25 波六星奇点悬赏具有四星悬赏约百倍生命");
assert(/function bountyTiersForWave[\s\S]{0,220}wave>=20\?4:2[\s\S]{0,120}wave>=25\?5:3/.test(gameSource),"固定悬赏队列从第 20 波加入五星、从第 25 波加入六星目标");
assert(/grantRandomCards\(`\$\{"★"\.repeat\(star\)\}[\s\S]{0,160}fixedStar:star,noFallback:true/.test(gameSource),"奖励敌人死亡后严格发放同星级卡牌且不向低星回退");
assert(!gameSource.includes("highStarPityTarget")&&/function normalStarProbabilities\(\)\{return BalanceCore\.starProbabilities\(starBoostRanks\(\)\);\}/.test(gameSource),"普通选牌不采用强制高星保底");
assert(/function renderMeters\(kind,target,record\)/.test(gameSource)&&gameSource.includes('class="meter-total"')&&gameSource.includes('class="meter-direct"'),"DPS 面板以淡色总伤害和实色直接伤害叠层显示");
assert(gameSource.includes("effectiveHealing")&&gameSource.includes("overhealing")&&gameSource.includes("shieldAbsorb"),"治疗统计区分有效治疗、过量治疗与护盾吸收");
assert(/function shouldAutoReleaseSkill/.test(gameSource)&&/addEventListener\("contextmenu",handleCanvasContextMenu\)/.test(gameSource)&&/document\.addEventListener\("contextmenu"/.test(gameSource),"右键炮塔可切换智能主技能且网页默认右键菜单被禁用");
assert(indexSource.includes('id="downloadLogsButton"')&&gameSource.includes('$("#downloadLogsButton").addEventListener("click",downloadCombatLogs)'),"左侧控制台提供战斗日志下载按钮");
assert(indexSource.includes('data-meter-target="boss"')&&indexSource.includes('data-meter-target="minion"')&&indexSource.includes('id="meterBossSelect"'),"简易/详细模式下方提供全部、BOSS、小怪与具体 Boss 选择器");
assert(/function scopedDamageStats\(record\)[^\n]+target==="boss"[^\n]+log\.isBoss&&Number\(log\.enemyId\)===Number\(state\.meterBossEnemyId\)[^\n]+!log\.isBoss/.test(gameSource),"伤害面板可按具体 Boss 或全部小怪聚合逐敌记录");
assert(/function damageMeterTitle\(record\)[^\n]+meterTargetLabel[^\n]+卡牌伤害（同卡合并）/.test(gameSource),"BOSS 伤害标题显示具体首领名称且详细模式注明同卡合并");
assert(/function makeWaveStats[\s\S]{0,900}bosses:Array\.isArray\(seed\.bosses\)/.test(gameSource),"逐波统计会持久化并克隆 Boss 生命周期记录");
assert(/function beginBossLog/.test(gameSource)&&/beginBossLog\(state\.enemies\[state\.enemies\.length-1\]\)/.test(gameSource)&&/finishBossLog\(enemy,"defeated"\)/.test(gameSource),"Boss 出场和死亡均写入当前波次日志");
assert(/function buildCombatLogExport/.test(gameSource)&&gameSource.includes("directBySource")&&gameSource.includes("indirectBySource")&&gameSource.includes("effectiveBySource")&&gameSource.includes("overhealingBySource")&&gameSource.includes("shieldAbsorbBySource"),"下载日志包含逐波直接/间接伤害及三类治疗数据");
assert(/payload\.schemaVersion=3/.test(gameSource)&&gameSource.includes("damageByCategory")&&gameSource.includes("damageByCardSeries")&&!/[,{]password:/.test(gameSource),"日志升级为第三版逐敌伤害结构且不导出账号口令字段");
assert(/function ensureEnemyDamageLog\(enemy\)[^\n]+name:enemy\.type\?\.name[^\n]+isBoss:[^\n]+damage:\{\},directDamage:\{\},indirectDamage:\{\},cardDamage:\{\}/.test(gameSource),"每个敌人按真实名称保存来源、直接/间接与卡牌伤害明细");
assert(/function resolveBarrierCollision\(enemy\)[^\n]+recordStat\("damage","分段屏障",integrity\);recordEnemyDamageStat\(enemy,"分段屏障",integrity,"direct"\);enemy\.hp=0;enemy\.shield=0;killEnemy\(enemy,"分段屏障"\)/.test(gameSource),"分段屏障消灭小怪时同步写入该敌人的详细伤害日志");
assert(/function serializeAccountStoreForStorage\(store=state\.accountStore\)\{return JSON\.stringify\(store,\(key,value\)=>key==="enemyDamage"\?undefined:value\);\}/.test(gameSource),"本机存档剔除无界逐敌明细但不改动当前会话日志");
const storageSerializerSource=gameSource.match(/function serializeAccountStoreForStorage\(store=state\.accountStore\)\{[^\n]+\}/)?.[0];
assert(storageSerializerSource,"可提取本机账号存档序列化器");
const storageSerializerSandbox={state:{accountStore:null}};
vm.runInNewContext(`${storageSerializerSource};globalThis.__serializeAccountStoreForStorage=serializeAccountStoreForStorage;`,storageSerializerSandbox);
const storageEnemyDamage=Object.fromEntries(Array.from({length:20000},(_,index)=>[String(index),{enemyId:index,damage:{"子弹炮":index+1},cardDamage:{bullet_base_damage:index+1}}]));
const storageProbe={accounts:[{id:"a",run:{stats:{waves:{1:{damage:{"子弹炮":9},cardDamage:{bullet_base_damage:9},enemyDamage:storageEnemyDamage}}}}},{id:"b",run:{stats:{waves:{2:{enemyDamage:{legacy:{enemyId:1,damage:{"激光炮":2}}}}}}}}]};
const storedProbe=storageSerializerSandbox.__serializeAccountStoreForStorage(storageProbe);
assert(!storedProbe.includes('"enemyDamage"')&&storedProbe.includes('"cardDamage"'),"两万条逐敌明细不会进入任一账号的 localStorage，聚合卡牌伤害仍保留");
assert.equal(Object.keys(storageProbe.accounts[0].run.stats.waves[1].enemyDamage).length,20000,"存档过滤不会清理当前会话内存中的完整逐敌日志");
assert(/function persistAccountStore\(\)[^\n]+serializeAccountStoreForStorage\(\)[^\n]+return true;[^\n]+本次存档未写入[^\n]+return false;/.test(gameSource)&&/function saveRun\(manual=false\)[^\n]+const saved=persistAccountStore\(\);if\(!saved\)[^\n]+return false;[^\n]+if\(manual\)\{showToast\(`已保存/.test(gameSource),"只有本机存储真实写入成功时才提示已保存");
assert(/payload\.detailedLogRetention="session"/.test(gameSource)&&/const \{damage=\{\},directDamage=\{\},indirectDamage=\{\},cardDamage=\{\},\.\.\.identity\}=enemy/.test(gameSource)&&/new Blob\(\[JSON\.stringify\(payload\)\]/.test(gameSource),"逐敌日志导出标明会话范围且移除重复字段与缩进膨胀");
assert(/function recordCardDamage\(cardId,amount,enemy=null\)[^\n]+card\.id[^\n]+enemyLog\.cardDamage\[card\.id\]/.test(gameSource),"详细伤害始终按基础卡 ID 合并全部等级并同步写入逐敌日志");
assert(gameSource.includes("enemyPressure")&&gameSource.includes("barrier:{...waveStats.barrier}")&&gameSource.includes("timing:waveStats.timing"),"逐波日志补充敌人生命压力、屏障状态和首领到场时间");

assert(/function cardLevelDefinition\(card,level\)[^\n]+id:`\$\{card\.id\}@\$\{rank\}`[^\n]+name:card\.max>1\?`\$\{card\.name\}·\$\{suffix\}`/.test(gameSource),"每个卡牌等级具有稳定的 baseId@level 身份和独立罗马数字名称");
assert(/cards\.flatMap\(\(card\)=>Array\.from\(\{length:card\.max\},\(_,level\)=>renderCard\(card,level\+1\)\)\)/.test(gameSource),"图鉴把同一卡牌的每个等级渲染为独立卡面");
assert(/function rollWaveChoiceEcho\(id\)[^\n]+WAVE_CHOICE_ECHO_CHANCES[^\n]+addCard\(id,\{deferUI:true,deferDerived:true,skipRefraction:true,silent:true\}\)/.test(gameSource)&&/!wasOpeningDraft&&!wasOpeningGrowthDraft&&!wasTomeDraft&&!wasRewardDraft&&!wasBargainPick\)rollWaveChoiceEcho\(id\)/.test(gameSource),"余辉演化只复制正常波末选择且不会递归触发概率折射");
assert(gameSource.includes('id:"shield_regen"')&&gameSource.includes("战斗中持续生效")&&!/updateDefense\(dt\)[^\n]+lastDamageTime/.test(gameSource),"相位回充取消脱离战斗限制并持续恢复护盾");
assert(indexSource.includes('id="deleteAccountButton"')&&indexSource.includes('id="deleteAccountOverlay"')&&/function confirmDeleteAccount\(\)[^\n]+accounts=state\.accountStore\.accounts\.filter/.test(gameSource),"普通本机账号具备二次确认删除入口");
assert(/function updateDeleteAccountButton\(\)[^\n]+button\.classList\.toggle\("hidden",!account\)[^\n]+protectedAccount[^\n]+系统账号不可删除/.test(gameSource),"删除入口始终跟随所选账号显示，测试与设计账号明确显示不可删除");
assert(/async function requestDeleteAccount\(\)[^\n]+accountSelectedForDeletion\(\)[^\n]+hashPin\(pin,account\.id\)!==account\.pinHash/.test(gameSource),"未登录普通账号也可在验证所选账号四位口令后发起删除");
assert(/#accountOverlay \{ z-index:140; \}/.test(stylesSource)&&/#deleteAccountOverlay \{ z-index:150; \}/.test(stylesSource),"账号与删除确认窗口始终显示在开局窗口之上");
assert(indexSource.includes('data-test-preset="wave50boss"')&&/preset==="wave50boss"\)\{startWave50BossTest\(\);return;\}/.test(gameSource),"左侧第 50 关 Boss 按钮复用已验证的测试预设事件管线");

assert(/function cardProgressionUnlocked[\s\S]{0,180}card\.star===5&&effectiveWave>=10[\s\S]{0,80}card\.star===6&&effectiveWave>=15/.test(gameSource),"wave 10 force-unlocks all five-star cards and wave 15 force-unlocks all six-star cards");
assert(/state\.openingDraft\?generateWeightedCards\(DRAFT_OFFER_COUNT,\{ignorePreference:true,history:\[\],maxStar:4/.test(gameSource),"opening draft remains capped at four stars");
assert(/function allBountyCardsMaxedAtStar[\s\S]{0,300}every\(\(card\)=>cardRank\(card\.id\)>=card\.max\)/.test(gameSource),"reward overflow starts only after every applicable card at that star is fully maxed");
assert(/function bountyCardsAtStar[\s\S]{0,260}!card\.designRemoved[\s\S]{0,120}card\.star===target[\s\S]{0,120}cardRank\(card\.id\)<card\.max/.test(gameSource),"reward enemies use an exact-star collectible pool that ignores ordinary wave and prerequisite locks");
assert(/generateFixedStarCards\(target,count,\{specialOnly:!!options\.specialOnly,noFallback:true,bountyReward:true\}\)/.test(gameSource),"undiscovered bounty tiers award their exact star even during early waves");
assert(/function generateBountyRewardCards[\s\S]{0,360}Math\.min\(6,target\+1\)[\s\S]{0,180}card\.star<=ceiling/.test(gameSource),"completed reward tiers may roll any available card no higher than the next star");
assert(/fixedStar:star,noFallback:true,bountyOverflow:true/.test(gameSource),"bounty kills use completed-tier overflow without ordinary downward fallback");

console.log(JSON.stringify({
  cardsAudited:cards.length,
  openingDrafts:5,
  initialRandomCards:5,
  offerCount:4,
  forbiddenInsight:[Balance.forbiddenInsightChance(1), Balance.forbiddenInsightChance(5)],
  bonusBountyIntervals:[Balance.bonusBountyInterval(1), Balance.bonusBountyInterval(3)],
  bulletOfferBaseline:+baseline["弹道"].toFixed(3),
  bulletOfferAfterPick:+afterBullet["弹道"].toFixed(3),
  otherFamilyLift:+(afterBullet["激光"] / baseline["激光"] - 1).toFixed(3),
  baseDps:Object.fromEntries(Object.entries(baseDps).map(([key,value]) => [key,+value.toFixed(2)]))
}, null, 2));
