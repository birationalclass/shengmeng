"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const vm = require("node:vm");
const path = require("node:path");
const Balance = require("../balance-core.js");

const gamePath = path.join(__dirname,"..","game.js");
const source = fs.readFileSync(gamePath,"utf8");
const end = source.indexOf("  const CARD_MAP =");
assert(end > 0,"能定位动态卡牌目录");
const prefix = `${source.slice(0,end)}\n  globalThis.__cards=CARDS;\n  globalThis.__activeSkillOrder=ACTIVE_SKILL_ORDER;\n})();`;
const canvas = {getContext:()=>({})};
const document = {querySelector:(selector)=>selector==="#gameCanvas"?canvas:{},querySelectorAll:()=>[]};
const sandbox = {console,document,window:{EndlessBalanceCore:{}},globalThis:null,Math,setTimeout,clearTimeout};
sandbox.globalThis=sandbox;
vm.runInNewContext(prefix,sandbox,{filename:"game-card-prefix.js"});
const allCards=sandbox.__cards;
const cards=allCards.filter((card)=>!card.designRemoved);
assert.deepEqual(Array.from(sandbox.__activeSkillOrder),["laser","frost","bullet","support","missile","arc"],"QWERTY 必须按画面从左到右对应激光、冰霜、子弹、支援、导弹、电弧");
const ids=new Set(cards.map((card)=>card.id));
const duplicateIds=allCards.map((card)=>card.id).filter((id,index,all)=>all.indexOf(id)!==index);
assert.equal(new Set(allCards.map((card)=>card.id)).size,allCards.length,`动态卡池 ID 不重复：${duplicateIds.join(",")}`);
assert(!ids.has("global_damage"),"旧弹道火控总成不再进入卡池");
const historicalBulletCards=allCards.filter((card)=>card.tags.includes("弹道")),bulletCards=cards.filter((card)=>card.tags.includes("弹道"));
assert.equal(historicalBulletCards.reduce((sum,card)=>sum+card.max,0),99,"弹道历史目录仍可识别 99 级原始总量");
assert.equal(bulletCards.reduce((sum,card)=>sum+card.max,0),93,"子弹炮真实可获取等级上限严格为 93");
assert.equal(historicalBulletCards.filter((card)=>card.designRemoved).map((card)=>card.id).join(","),"evo_bullet_3_4,evo_bullet_4_4,evo_bullet_6_4","奇点弹仓废卡的 6 个等级不进入可获取统计");
for(const card of allCards){assert(card.star>=1&&card.star<=6,`${card.id} 星级合法`);assert(card.max>=1&&card.max<=6,`${card.id} 等级上限合法`);}

const families={bullet:"弹道",laser:"激光",missile:"导弹",frost:"冰霜",arc:"电弧",support:"支援"};
for(const [turret,family] of Object.entries(families)){
  const basics=cards.filter((card)=>card.star===1&&card.tags.includes(family));
  assert(basics.length>=5,`${family} 至少五张一星基础卡`);
  const basicIds=turret==="support"?["support_base_heal","support_base_crit","support_base_crit_power","support_base_duration","support_overheal_fortification"]:[`${turret}_range`,`${turret}_base_rate`,`${turret}_base_damage`,`${turret}_base_crit`,`${turret}_base_crit_power`];
  for(const id of basicIds){
    assert(ids.has(id),`${family} 基础卡 ${id} 存在`);
    assert.equal(cards.find((card)=>card.id===id).max,5,`${id} 具有五级成长`);
  }
  assert(ids.has(`${turret}_active_skill`),`${family} 四星主动技能存在`);
  if(turret==="bullet")assert(!ids.has("bullet_skill_cooldown")&&!ids.has("bullet_skill_power"),"弹道旧超载衍生系列已移除，仅保留弹幕全开主动核心");
  else assert(ids.has(`${turret}_skill_cooldown`)&&ids.has(`${turret}_skill_power`),`${family} 五星主动技能分支存在`);
  const minimums=turret==="bullet"?[5,5,5,4,3,1]:turret==="support"?[5,5,5,4,4,3]:[5,5,5,4,4,4];
  for(let star=1;star<=6;star++)assert(cards.filter((card)=>card.star===star&&card.tags.includes(family)).length>=minimums[star-1],`${family} ★${star} 满足当前机制卡数量下限`);
}
for(const id of ["cryo_missile_echo","laser_arc_echo","missile_arc_echo","support_laser_echo"]){const card=cards.find((item)=>item.id===id);assert.equal(card.star,6,`${id} 为六星连携`);}
for(const id of ["laser_photon_memory","missile_recursive_swarm","frost_zero_archive","arc_storm_crown"]){const card=cards.find((item)=>item.id===id);assert(card?.selfApex&&card.star===6,`${id} 为对应炮塔的六星自成体系卡`);}
assert(ids.has("support_base_duration")&&ids.has("support_base_crit_power"),"支援一星同时具备机器人持续时间与治疗暴击量成长");
assert.equal(cards.find((card)=>card.id==="support_base_rate")?.star,2,"发射机器人速率已归入二星支援卡");
for(const removedId of ["support_medic","support_nanite_covenant","emergency_repair"]){assert(!ids.has(removedId),`${removedId} 已从卡池移除`);}
assert(!ids.has("support_range")&&ids.has("support_overheal_fortification"),"支援全屏治疗不再占用射程卡槽，并新增一星溢疗筑垒");
assert(allCards.find((card)=>card.id==="streak_forge")?.designRemoved&&!ids.has("streak_forge"),"连杀锻炉仅保留历史目录标记，不再进入实际可获取卡池");
const waveChoiceEcho=cards.find((card)=>card.id==="wave_choice_echo");
assert(waveChoiceEcho?.star===1&&waveChoiceEcho.max===5,"余辉演化是一星五级特殊卡");
assert(waveChoiceEcho.desc(0).includes("10%")&&waveChoiceEcho.desc(4).includes("25%"),"余辉演化由 10% 成长至 25% 波末额外升级概率");
assert.equal(cards.find((card)=>card.id==="frost_field")?.star,3,"多重减速已归入冰霜三星卡");
const foundationApexCards=new Set(["bullet_base_crit","laser_base_crit","missile_base_crit","frost_base_crit","arc_base_crit","support_base_crit","bullet_base_crit_power","arc_base_crit_power","frost_base_crit_power"]);
for(const card of cards.filter((item)=>item.star===1&&item.max===5&&item.passive?.values?.length===5)){if(/_base_(damage|rate)$/.test(card.id)||card.id==="support_base_duration"||card.id==="support_base_heal")continue;const values=card.passive.values,previous=values[3],lastGain=values[4]-values[3],ratio=lastGain/Math.max(.0001,previous);if(foundationApexCards.has(card.id))assert(ratio>=1.49&&ratio<=4,`${card.id} 第五级执行指定的基础数值大幅质变`);else assert(ratio>=.8&&ratio<=2,`${card.id} 第五级边际成长处于前四级累计的 80%–200%`);}
assert.deepEqual(Array.from(cards.find((card)=>card.id==="support_base_heal").passive.values),[1,1.5,2,3,5],"基础治疗额外系数按 1.0/1.5/2.0/3.0/5.0 成长");
assert.deepEqual(Array.from(cards.find((card)=>card.id==="support_base_duration").passive.values),[1,2,3,4,7],"机器人持续时间从基础 1 秒成长为 2/3/4/5/8 秒");
assert.equal(cards.filter((card)=>card.tags.includes("特殊")).reduce((sum,card)=>sum+card.max,0),129,"特殊卡真实可获取等级上限严格为 129");
for(let star=1;star<=6;star++)assert(cards.some((card)=>card.star===star&&card.tags.includes("特殊")),`实际可获取目录仍覆盖 ★${star} 特殊卡`);
assert(!ids.has("blood_bargain")&&![3,4,5,6].some((star)=>ids.has(`forbidden_tome_${star}`)),"禁忌抄本只保留二星版本");
const forbiddenTome=cards.find((card)=>card.id==="forbidden_tome_2");
assert(forbiddenTome?.max===5&&forbiddenTome.desc(4).includes("★6 卡牌 4 选 1"),"禁忌抄本第五级追加六星卡牌四选一");
assert.deepEqual(Array.from(cards.find((card)=>card.id==="frost_trace_spread_2").passive.values),[.5,.75,1],"霜痕扩散从 50% 起步并成长至行动速度翻倍");
assert.deepEqual(Array.from(cards.find((card)=>card.id==="laser_base_rate").passive.values),[.1667,.3333,.5,.6667,1],"激光基础攻速由初始 6/分成长为 7/8/9/10/12 每分");
assert(source.includes('分别修复每段最大生命的 20%')&&source.includes('repairBySegment=state.barrierSegments.map'),"净界维修蜂群采用五段分别按最大生命百分比修复");
assert(source.includes('function drawBarrierSegmentStatuses')&&source.includes('kind:"brokenHeart"')&&source.includes('kind:"minus"')&&source.includes('function barrierTangentAngle'),"五段屏障沿弧线分别绘制左侧增益与右侧减益层数图标");
for(const id of ["turret_laser","turret_missile","turret_frost","turret_arc","turret_support"]){
  assert(!ids.has(id),`${id} 部署牌已从卡池移除`);
}
for(const id of ["frost_ammo","frost_group_slow_2","frost_single_slow_2","frost_slow_echo_2","frost_bounty_flower","cryo_arc_bridge","frost_laser_resonance","thermal_rupture","frost_support_preservation"]){
  assert(ids.has(id),`${id} 冰霜构筑卡存在`);
}
assert.equal(cards.find((card)=>card.id==="cryo_arc_bridge").star,4,"电离寒潮归入冰霜四星联动");
assert(cards.find((card)=>card.id==="frost_laser_resonance").tags.includes("激光"),"冷光共振同时属于激光卡牌");
assert(cards.find((card)=>card.id==="thermal_rupture").tags.includes("导弹"),"冷热破碎同时属于导弹卡牌");
assert(cards.find((card)=>card.id==="frost_support_preservation").tags.includes("支援"),"寒气续航同时属于支援卡牌");

const replacementLaserControls=[
  {id:"evo_laser_2_4",name:"迟滞棱镜·Ⅱ",star:2,max:3,minWave:2,req:[],first:["0.15 秒","Boss 持续时间减半"],last:["0.35 秒"]},
  {id:"evo_laser_3_4",name:"光压回卷·Ⅲ",star:3,max:3,minWave:4,req:[],first:["每第 3 轮","20","0.35 秒"],last:["50","0.75 秒"]},
  {id:"evo_laser_4_4",name:"分光囚笼·Ⅳ",star:4,max:2,minWave:6,req:["laser_reflect"],first:["首脉冲","反射命中","0.55 秒","每轮 1 次"],last:["0.9 秒"]}
];
for(const expected of replacementLaserControls){
  const card=cards.find((item)=>item.id===expected.id);
  assert(card,`${expected.id} 替代短控卡保留稳定存档 ID`);
  assert.equal(card.name,expected.name,`${expected.id} 使用新的特色名称`);
  assert.equal(card.star,expected.star,`${expected.name} 星级正确`);
  assert.equal(card.max,expected.max,`${expected.name} 等级上限正确`);
  assert.equal(card.minWave,expected.minWave,`${expected.name} 最早波次正确`);
  assert.deepEqual(Array.from(card.req||[]),expected.req,`${expected.name} 前置依赖正确`);
  assert(card.tags.includes("激光")&&card.tags.includes("功能"),`${expected.name} 归入激光功能卡`);
  for(const text of expected.first)assert(card.desc(0).includes(text),`${expected.name} 首级文案包含 ${text}`);
  for(const text of expected.last)assert(card.desc(card.max-1).includes(text),`${expected.name} 满级文案包含 ${text}`);
}
assert(!cards.some((card)=>card.name.startsWith("无限折光·")),"旧无限折光占位系列已完全退出运行时卡池");

const counts=Object.fromEntries(Object.entries(families).map(([key,tag])=>[key,cards.filter((card)=>card.tags.includes(tag)).length]));
const starCounts=Array.from({length:6},(_,index)=>cards.filter((card)=>card.star===index+1).length);
const specialStarCounts=Array.from({length:6},(_,index)=>cards.filter((card)=>card.star===index+1&&card.tags.includes("特殊")).length);
const fullRanks=new Map(cards.map((card)=>[card.id,card.max]));
const terminalProfiles=Object.fromEntries(Object.entries(families).map(([key,tag])=>{const profile=Balance.terminalSynergyProfile(cards,fullRanks,tag);return [key,{...profile,multiplier:+profile.multiplier.toFixed(2)}];}));
const terminalMultipliers=Object.fromEntries(Object.entries(terminalProfiles).map(([key,profile])=>[key,profile.multiplier]));
for(const [family,multiplier] of Object.entries(terminalMultipliers)){const floor=family==="bullet"?5:15;assert(multiplier>=floor&&multiplier<=40,`${family} 全卡终局乘区处于当前机制目标区间`);}
const historicalWave40Dps=41600,historicalWave40Hps=1785;
const observedDamageShares={bullet:.026,laser:.412,missile:.338,frost:.017,arc:.191,support:.016};
const weightedTerminalMultiplier=Object.entries(observedDamageShares).reduce((sum,[family,share])=>sum+share*terminalMultipliers[family],0);
const projectedFullCardDps=historicalWave40Dps*weightedTerminalMultiplier;
const wave40NaturalHp=36*Math.pow(1.15,39)*(1+20*.018),wave40BarrierBase=(78+wave40NaturalHp*1.35)*Balance.lateWaveProfile(40).barrierScale;
const projectedFullCardBarrier=wave40BarrierBase*(1+(terminalMultipliers.support-1)*1.35);
const projectedFullCardHps=projectedFullCardBarrier*.8/.75;
assert(projectedFullCardDps>=900000&&projectedFullCardDps<=1350000,"第 40 波全卡理论 DPS 应稳定在约 1m");
assert(projectedFullCardHps>=750000&&projectedFullCardHps<=1250000,"第 40 波全卡压力治疗 HPS 应稳定在约 1m");
assert(source.includes('radius:ZERO_FIELD_RADIUS,power:.45')&&!source.includes('radius:FULL_SCREEN_RANGE,power:.45'),"绝对零度使用有效半径字段，不再生成无效全屏渐变");
assert(source.includes('if(enemy.stun>0||isEnemyFrozen(enemy))continue;'),"绝对零度只冻结非首领单位的更新，不删除敌人");
assert(source.includes('updateCombatJobs();updateTurrets'),"高负载主动技能工作按帧预算执行");
console.log(JSON.stringify({totalCards:cards.length,counts,starCounts,specialStarCounts,terminalProfiles,projectedFullCardDps:Math.round(projectedFullCardDps),projectedFullCardHps:Math.round(projectedFullCardHps),projectedFullCardBarrier:Math.round(projectedFullCardBarrier)},null,2));
