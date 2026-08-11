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
const cardPrefix = `${gameSource.slice(0,cardEnd)}\n  globalThis.__cards=CARDS;\n})();`;
const cardCanvas = {getContext:()=>({})};
const cardDocument = {querySelector:(selector)=>selector==="#gameCanvas"?cardCanvas:{},querySelectorAll:()=>[]};
const cardSandbox = {console,document:cardDocument,window:{EndlessBalanceCore:{}},globalThis:null,Math,setTimeout,clearTimeout};
cardSandbox.globalThis=cardSandbox;
vm.runInNewContext(cardPrefix,cardSandbox,{filename:"game-card-prefix.js"});
const cards = cardSandbox.__cards;

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
assert(/openingRewardCards=initialCards\.map/.test(gameSource)&&/随机 \$\{rewards\.length\} · 已选 \$\{picks\.length\}/.test(gameSource), "开局随机奖励与逐次手选卡牌持续展示在初始构筑区");
assert(/const INITIAL_BARRIER_SEGMENT_HP = 100;/.test(gameSource), "五段小屏障各自以一百生命开始");
assert(!cards.some((card) => card.id === "global_damage"), "已删除弹道火控总成");
assert.equal(cards.find((card) => card.id === "bullet_base_damage").max, 5, "子弹基础攻击卡使用五级质变成长");
const baseAttackProfiles = {
  bullet:{values:[.9,1.8,2.6,3.4,5],flatValues:[90,180,260,340,500]},
  laser:{values:[.05,.1,1,3,10],flatValues:[25,50,500,1500,5000]},
  missile:{values:[.05,.1,1,3,10],flatValues:[25,50,500,1500,5000]},
  frost:{values:[.25,.55,.95,1.5,2.5],flatValues:[5,11,19,30,50]},
  arc:{values:[.45,.9,1.3,1.7,2.5],flatValues:[45,90,130,170,250]}
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
assert(/addCard\(id,wasOpeningDraft\?\{deferUI:true,skipDerived:true,manualPick:true\}:\{deferUI:true,deferDerived:true,manualPick:true\}\);if\(!wasOpeningDraft\)rememberCardChoice/.test(gameSource), "选卡点击不在当前帧重建全部界面，连续初始选卡仅在结束时提交派生状态");
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
assert(/spendBarrierHealth\(cost,1\)/.test(gameSource)&&/profile\.costRate/.test(gameSource), "禁忌抄本从分段屏障生命支付百分比代价");
assert(!/showDraft\(false,true\)/.test(gameSource), "旧禁忌洞见额外选卡入口已停用");
assert(/fixedStar:star/.test(gameSource), "限时猎物按自身星级直接随机发放同星卡牌");
assert(!/rewardDraftsQueued\+=rewards/.test(gameSource), "新奖励敌人不再排队弹出选卡面板");
assert(/function rollProbabilityRefraction\(/.test(gameSource), "概率折射在选取同星卡后判定附赠卡");
assert(!cards.some((card)=>card.id.startsWith("fate_reroll_"))&&!/FATE_REROLL_BONUSES|fateRerollBonus/.test(gameSource), "命运重排卡牌及刷新加成逻辑已彻底移除");
assert(/function starlightRoadProfiles\(/.test(gameSource)&&/function rollStarlightRoadBounties\(enemy\)/.test(gameSource), "一至四星星光大道分别累计普通敌人击杀并独立生成奖励敌人");
assert(/STARLIGHT_ROAD_INTERVALS=Array\.from\(\{length:4\},\(\)=>\[30,25,20,15,10\]\)/.test(gameSource), "星光大道五级所需击杀数由 30 递减至 10");
assert(/STARLIGHT_ROAD_CHANCES=Array\.from\(\{length:4\},\(\)=>\[\.30,\.35,\.40,\.45,\.50\]\)/.test(gameSource), "星光大道触发率由 30% 成长至 50%");
assert(/projectile\.frostCarrier=true/.test(gameSource), "低温弹药把命中减速目标后的子弹转为寒冰载体");
assert(/spreadLimit=\[0,2,4,6\]/.test(gameSource)&&/decay=\[0,\.68,\.78,\.88\]/.test(gameSource), "电离寒潮按数量和逐跳衰减传染减速");
assert(/chilledPierces\+=1/.test(gameSource)&&/frost_laser_resonance/.test(gameSource), "激光穿透减速目标会逐段增伤");
assert(/coldDuration=Math\.min\(1,slowedEnemies/.test(gameSource), "减速目标数量最多使维修机器人持续时间翻倍");
assert(/if\(enemy\.frostFlower\)grantRandomCards\("霜之花绽放",1,\{fixedStar:star,specialOnly:true,noFallback:true\}\)/.test(gameSource), "霜之花击杀奖励同星特殊卡牌");

assert(/function waveBossType\(\)\{const blackHoles=/.test(gameSource), "守关首领从黑洞序列选择");
assert(/function waveMidBossType\(\)/.test(gameSource), "恒星作为波次中途小首领出现");
assert(/function finalBossEntries\(wave=state\.wave\)\{if\(wave<10\)return \[\]/.test(gameSource), "前九波不生成终局黑洞首领");
assert(/double=wave%9===0\|\|wave%13===0/.test(gameSource), "中后期存在双黑洞守关日程");
assert(/colossal:wave%3===0/.test(gameSource), "每三波的守关日程生成巨型黑洞");
assert(/function isRedGiantFinalWave\(wave=state\.wave\)\{return wave>=15&&wave%10===5/.test(gameSource), "十五波起部分特色关以红巨星作为终局首领");
assert(/type\.radius\*\(colossal\?2\.1:1\)/.test(gameSource), "巨型黑洞碰撞与画面尺寸至少扩大两倍");
assert(/const MAX_COLOSSAL_BOSS_WIDTH = 660;/.test(blackHoleSource), "巨型黑洞素材允许扩展到压迫性宽度");
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
assert(/function starBossMoveScale\(enemy\)/.test(gameSource), "恒星小首领拥有快速入场到正常巡航的平滑曲线");
assert(/enemy\.y\+=enemy\.speed\*\(redGiant\?1\.65:starBossMoveScale\(enemy\)\)\*dt/.test(gameSource), "恒星小首领与红巨星分别接入推进倍率");
assert(/id="speedButton"/.test(indexSource) && /function toggleGameSpeed\(\)/.test(gameSource), "左侧控制区提供一倍与二倍游戏速度切换");
assert(/const DISTANCE_DAMAGE_MIN = \.5;/.test(gameSource), "战区最远端获得百分之五十伤害减免");
assert(/function distanceDamageMultiplier\(enemy\)[\s\S]{0,260}DISTANCE_DAMAGE_MIN\+\(1-DISTANCE_DAMAGE_MIN\)\*progress/.test(gameSource), "远距减伤向屏障前线性衰减至零");
assert(/multiplier=options\.trueDamage\?1:defense\*distanceMultiplier/.test(gameSource), "普通伤害接入纵深减伤，六相百分比真实伤害可绕过");
assert(/const DISTANCE_BALANCE_HP_SCALE = \.88;/.test(gameSource), "敌方基础生命下调以补偿新增纵深减伤");
assert(/if\(!opening&&!state\.draftWaveStarted\)\{repairAfterWave\(\);startNextWave\(\);state\.draftWaveStarted=true;\}/.test(gameSource), "波次奖励弹窗出现前已立即启动下一波");
assert(/draftPause:true/.test(gameSource)&&/id="draftPauseInput"/.test(indexSource), "设置提供独立的后续选卡暂停开关且默认开启");
assert(/state\.paused=!!opening\|\|state\.settings\.draftPause/.test(gameSource), "初始选卡始终暂停，后续选卡服从独立设置");
assert(/下一波已开始 · \$\{state\.settings\.draftPause\?"战斗已暂停":"战斗继续"\}/.test(gameSource), "后续选卡明确显示当前暂停状态");
assert(/state\.paused=state\.settings\.draftPause/.test(gameSource), "禁忌抄本选卡同样服从后续选卡暂停设置");

assert(/function subwaveCountForWave\(wave\)\{return Math\.min\(8,3\+/.test(gameSource), "第一波固定从三个小波起步并随波次增加");
assert(/function isInterwaveFillerSlot\(/.test(gameSource)&&/function spawnCadenceForWave\(/.test(gameSource), "小波之间使用低密度零星敌人填充并设置独立间隔");
assert(/function subwaveRestDuration\(wave,scenario=state\.waveScenario\|\|waveScenario\(wave\)\)\{return Math\.max\(3\.2,\(3\.8\+Math\.min\(1\.2,wave\*\.04\)\)\*Math\.max\(\.86,scenario\.spawnScale\)\);\}/.test(gameSource), "小波衔接休整时间显著拉长且高速特色波也保留至少三点二秒间隔");
assert(/waveBaseTarget:state\.waveTarget/.test(gameSource), "小波节奏使用基础刷怪数，不受分裂与召唤临时扩容干扰");
assert(/base=\(20\+wave\*3\.4\+Math\.pow\(wave,1\.1\)\*1\.25\)/.test(gameSource), "每波普通敌人总量采用扩容后的成长曲线");
assert(/function openingEnemyHpMultiplier\(wave=state\.wave\)\{return wave<=5\?\.7:1;\}/.test(gameSource), "前五波敌方生命统一降低百分之三十");
assert(/function earlySmallEnemyHpMultiplier\(type,wave=state\.wave\)\{return wave<=10&&!type\.boss&&!type\.bounty&&!type\.summoned\?\.8:1;\}/.test(gameSource), "前十波普通小怪额外降低百分之二十生命且不影响奖励、召唤与首领单位");
assert(/waveBaseHp\(\)\*earlySmallEnemyHpMultiplier\(type\)\*DISTANCE_BALANCE_HP_SCALE/.test(gameSource), "普通小怪生命倍率接入实际生成数值");
assert(/function normalEnemySpeedMultiplier\(type\)\{return !type\.boss&&!type\.bounty&&!type\.summoned\?\.8:1;\}/.test(gameSource), "所有普通小怪移动速度统一降低百分之二十");
assert(/type\.speed\*normalEnemySpeedMultiplier\(type\)\*\(type\.boss\?\.6:1\)/.test(gameSource), "普通小怪速度倍率接入实际生成速度且不改变首领与奖励单位");
assert(/function turretFormationY\(x\)\{return Math\.round\(1138\+\(barrierSurfaceY\(x\)-barrierSurfaceY\(W\/2\)\)\*\.36\);\}/.test(gameSource), "六座炮塔按屏障圆弧曲率排布并让两侧炮塔适当下沉");
assert(/\.\.\.def,y:turretFormationY\(def\.x\),id,active:/.test(gameSource), "所有炮塔实例统一使用圆弧阵列纵坐标");
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
assert(/difficultyFactors\(\)\.hp/.test(gameSource) && /difficultyFactors\(\)\.attack/.test(gameSource), "层级难度同时调整生命、攻击与数量");
assert(/function allCardsMaxed\(\)/.test(gameSource) && /collectionCompleteWave\+5/.test(gameSource), "卡牌全收集后再守五波触发通关");
for(const relic of ["vanguard_chart","supply_capsule","barrier_seed","time_prism"])assert(gameSource.includes(`id:"${relic}"`), `遗物 ${relic} 已实现`);
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
assert(/bullet:\{flatMax:500,multiplierMax:5,critPowerMax:10,curve:"standard",attackCurve:"front"\}/.test(gameSource), "子弹基础攻击前两级快速成长");
assert(/missile:\{flatMax:5000,multiplierMax:10,critPowerMax:20,curve:"burst",attackCurve:"compressed"\}/.test(gameSource)&&/laser:\{flatMax:5000,multiplierMax:10,critPowerMax:20,curve:"burst",attackCurve:"compressed"\}/.test(gameSource), "导弹与激光前两级严格为满级的百分之零点五与百分之一");
assert(/arc:\{flatMax:250,multiplierMax:2\.5,critPowerMax:5,curve:"standard",attackCurve:"front"\}/.test(gameSource)&&/frost:\{flatMax:50,multiplierMax:2\.5,critPowerMax:5,curve:"standard",attackCurve:"steady"\}/.test(gameSource), "电弧前置成长且冰霜保持平稳成长");
assert(/const BASE_RATE_TARGETS=\{/.test(gameSource)&&!/baseRateCooldownFactor/.test(gameSource), "基础攻速直接以各炮塔实际射速为目标且不再叠加隐藏后摇");
assert(/function turretDamageMultiplier\(turretId\)\{return \(1\+turretPassive\(turretId,"damage"\)\)\*terminalSynergy/.test(gameSource), "基础攻击不再重复叠加隐藏的满级增伤");
assert(/fullScreen:rank>=5/.test(gameSource)&&/stat\.fullScreen\?"满屏"/.test(gameSource), "满级射程直接显示满屏而不是数值");
assert(/boostedAttackStat=turretId!=="support"&&\(stat==="damage"\|\|stat==="critPower"\)/.test(gameSource), "二至六星攻击与暴伤卡统一使用双倍成长规则");
assert(/flatValues=stat==="damage"&&turretId!=="support"\?Array\.from\(\{length:max\},\(_,index\)=>star\*\(index\+1\)\):null/.test(gameSource), "每级攻击卡额外加入等于星级的固定攻击");
assert(/turret\.damage=TURRET_DEFS\[turretId\]\.damage\+turretFlatDamage\(turretId\)/.test(gameSource), "炮塔先汇总初始攻击与固定攻击，再交给攻击提升系数结算");
assert(/node\.dataset\.updateAverage=updateTiming\.average\.toFixed\(3\)/.test(gameSource), "测试档案分别记录战斗更新耗时");
assert(/node\.dataset\.drawAverage=drawTiming\.average\.toFixed\(3\)/.test(gameSource), "测试档案分别记录画布绘制耗时");
assert(/node\.dataset\.crowdLod=String\(living\.length>CROWD_LOD_HARD_LIMIT\?2:living\.length>CROWD_LOD_SOFT_LIMIT\?1:0\)/.test(gameSource), "测试遥测会标记当前密集潮视觉等级");
assert(/data-test-preset="stress">满卡无敌压力 · 第 5 波/.test(indexSource), "测试账号提供第 5 波满卡无敌压力入口");
assert(/data-test-preset="stress40">满卡无敌压力 · 第 40 波/.test(indexSource), "测试账号提供第 40 波满卡无敌压力入口");
assert(/stress40:\{wave:40,cards:null,invincible:true\}/.test(gameSource), "第 40 波压力档启用满卡与双方无敌规则");
assert(/stress:\{wave:5,cards:null,invincible:true\}/.test(gameSource), "满卡压力预设从第 5 波启动并启用双方无敌");
assert(/if\(state\.qaInvincible\)\{enemy\.hit=\.08;return 0;\}/.test(gameSource), "无敌压力模式保留命中特效但不削减敌军生命");
assert(/function damageCore\([\s\S]{0,180}state\.qaInvincible/.test(gameSource), "无敌压力模式不削减五段屏障");
assert(/function damageMiniTurret\([^\n]+state\.qaInvincible/.test(gameSource), "无敌压力模式保护友方子炮塔");
assert(/state\.qaInvincible&&enemy\.y\+enemyRadius\(enemy\)>=barrierSurfaceY\(enemy\.x\)[\s\S]{0,240}state\.waveResolved\+=1/.test(gameSource), "敌军仅在实际触及屏障后从压力场景移除");
assert(/const active=state\.started&&!state\.paused&&!state\.gameOver,shouldDraw=active\|\|time-lastDraw>=1000\/18/.test(gameSource), "战斗中逐 RAF 绘制，暂停时才降至低刷新率");
assert(/node\.dataset\.drawGapAverage=drawGapTiming\.average\.toFixed\(2\)/.test(gameSource), "测试遥测记录真实绘制间隔以识别帧节奏问题");
assert(/function basicCardStatSentence\([\s\S]{0,900}formatCompactNumber\(Math\.round\(stat\.value\)\)/.test(gameSource), "基础数值卡使用整数紧凑格式展示当前值与升级后数值");
assert(/function formatDisplayNumber\([\s\S]{0,260}toFixed[\s\S]{0,180}function normalizeDisplayNumbers/.test(gameSource), "卡牌说明统一裁剪浮点尾数并移除无意义零位");
assert(/formatShotRate\(rate\)\{return Number\(rate\.toFixed\(3\)\)\.toString\(\)/.test(gameSource)&&/formatShotRate\(stat\.perSecond\)/.test(gameSource), "每秒攻击频率最多显示三位有效小数");
assert(/renderCard=\(card\)=>[\s\S]{0,1200}description=basicCardStatSentence\(card,rank\)\|\|normalizeDisplayNumbers\(card\.desc/.test(gameSource), "卡牌总览统一清理非整数显示");
assert(/renderDraft\(\)[\s\S]{0,700}description=basicCardStatSentence\(card,current\)\|\|draftCardDescription/.test(gameSource), "所有选牌弹窗的基础数值卡只显示精简升级数值");
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
for(const id of ["cryo_missile_echo","laser_arc_echo","bullet_support_echo"])assert(gameSource.includes(`id:"${id}"`),`六星主动联动 ${id} 已加入`);
const frostMultishot=cards.find((card)=>card.id==="frost_field"),overhealFortification=cards.find((card)=>card.id==="support_overheal_fortification");
assert.equal(frostMultishot.star,3,"多重减速归入三星冰霜构筑");
assert.deepEqual([0,1,2,3,4].map((rank)=>frostMultishot.desc(rank)),["每次发射 1 枚冰弹，并有 50% 概率额外发射第 2 枚。","每次稳定发射 2 枚冰弹。","每次稳定发射 3 枚冰弹，并有 50% 概率追加第 4 枚。","每次稳定发射 4 枚冰弹。","质变：每次稳定发射 5 枚冰弹。"],"多重减速按概率曲线成长并在五级稳定五发");
assert(/function rollFrostShotCount/.test(gameSource)&&/targets=\[target,\.\.\.alternatives\][\s\S]{0,180}while\(targets\.length<shotCount\)targets\.push\(target\)/.test(gameSource),"冰弹优先分配给不同目标，不足时才重复锁定");
assert(!/const station=cardRank\("frost_field"\)/.test(gameSource),"多重减速不再沿用寒冰基站的范围场逻辑");
assert(overhealFortification?.star===1&&overhealFortification.max===5,"溢疗筑垒是一星五级支援卡");
assert(/function fortifySegmentFromOverheal/.test(gameSource)&&/segment\.overhealBonus/.test(gameSource)&&/strictPreferred&&preferred/.test(gameSource),"机器人过量治疗只强化其附着分段并保留永久上限成长");
assert(/SUPPORT_OVERHEAL_CHANCES = \[\.10,\.20,\.25,\.30,\.35,\.50\]/.test(gameSource)&&/SUPPORT_OVERHEAL_RATES = \[\.01,\.012,\.014,\.016,\.018,\.02\]/.test(gameSource)&&/Math\.ceil\(overflow\*SUPPORT_OVERHEAL_RATES\[rank\]\)/.test(gameSource),"溢疗筑垒以 10% 基础概率成长至 50%，转化率由 1% 成长至 2%");
assert(/SUPPORT_OVERHEAL_PICK_BONUSES = \[0,100,200,300,400,500\]/.test(gameSource)&&/options\.manualPick[\s\S]{0,120}SUPPORT_OVERHEAL_PICK_BONUSES\[rank\]/.test(gameSource),"手动选取溢疗筑垒按等级立即提供 100 至 500 点五段总生命上限");
assert(/id:"support_overheal_shield"[\s\S]{0,260}SUPPORT_OVERHEAL_SHIELD_RATES/.test(gameSource)&&/function convertOverhealToShield/.test(gameSource),"二星溢疗护盾卡把附着段过量治疗转为可叠加护盾");
assert(/segment\.overhealShieldBonus=\(segment\.overhealShieldBonus\|\|0\)\+gain/.test(gameSource)&&/segment\.maxShield=desiredTotal\*share\+overhealShieldBonus/.test(gameSource),"机器人溢疗护盾永久记录在附着段，派生属性重算不会吞掉已转化护盾上限");
assert(/SUPPORT_OPERATION_RATES = \[3,5,6,7,8,10\]/.test(gameSource)&&/SUPPORT_HEAL_FREQUENCIES = \[1,1\.2,1\.4,1\.6,1\.8,2\.5\]/.test(gameSource),"机器人发射批次与单机器人治疗频率独立成长");
assert(/SUPPORT_HEAL_FIXED_VALUES = \[5,10,25,45,70,100\]/.test(gameSource)&&/SUPPORT_HEAL_MULTIPLIERS = \[1,1,1\.5,2,3,5\]/.test(gameSource)&&/SUPPORT_DURATION_VALUES = \[1,2,3,4,5,8\]/.test(gameSource),"基础治疗未选卡为 5、首级为 10，并按额外系数 1.0 至 5.0 与指定持续时间曲线成长");
assert(gameSource.includes('function supportBaseHealing(rank=cardRank("support_base_heal"))')&&gameSource.includes('(SUPPORT_HEAL_FIXED_VALUES[level]+(state.supportHealGrowth||0))*SUPPORT_HEAL_MULTIPLIERS[level]')&&/healing=supportBaseHealing\(\)/.test(gameSource),"支援单次治疗统一使用固定值、额外系数与击杀成长公式");
assert(/id:"support_kill_healing"[\s\S]{0,220}star:3,max:5/.test(gameSource)&&/SUPPORT_KILL_HEAL_GAINS = \[0,1,2,3,4,5\]/.test(gameSource)&&/growSupportHealingFromKill\(enemy\)/.test(gameSource),"三星生命回收协议按击杀永久提供 1 至 5 点基础治疗量");
assert(/supportHealGrowth:state\.supportHealGrowth\|\|0/.test(gameSource)&&/supportHealGrowth:Math\.max\(0,Number\(run\.supportHealGrowth\)\|\|0\)/.test(gameSource),"击杀获得的基础治疗量成长随存档保存与恢复");
assert(/REFRACTION_CHANCES=\[\.40,\.60,\.80,1,1\]/.test(gameSource)&&/count:rank>=5\?2:1/.test(gameSource),"所有星级概率折射统一从 40% 起步，四级必得 1 张、五级质变为 2 张");
assert(/grantRandomCards\("概率折射",refractionReward\.count,\{fixedStar:refractionReward\.star\}\)/.test(gameSource),"概率折射按质变后的奖励张数发放对应星级卡牌");
assert(/SUPPORT_CRIT_MULTIPLIERS = \[2,2\.5,3,4,5,10\]/.test(gameSource),"治疗暴击量从基础 200% 成长至质变 1000%");
assert(/ratios=\[0,\.3,\.45,\.6,\.8,2\]/.test(gameSource),"相位护盾五级质变上限为屏障生命的 200%");
assert(/thresholds=\[0,7,7,6,6,5\],gains=\[0,1,2,3,4,10\]/.test(gameSource),"连杀锻炉使用一星质变成长曲线");
assert(/function bountyMasteryTier/.test(gameSource)&&/bountyMasteryTier\(\)\*\.8/.test(gameSource)&&/bountyMasteryTier\(\)>=6/.test(gameSource),"悬赏统御协议按已拥有卡牌等级总数成长");
assert(gameSource.includes('if(stat==="baseHeal")return {label:"单次治疗",value:supportBaseHealing(rank),unit:""}'),"基础治疗量在图鉴与选牌中显示单次治疗数值变化");

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
