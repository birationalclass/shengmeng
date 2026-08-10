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
const cards=sandbox.__cards;
assert.deepEqual(Array.from(sandbox.__activeSkillOrder),["laser","frost","bullet","arc","missile","support"],"1—6 必须按画面从左到右对应激光、冰霜、子弹、电弧、导弹、支援");
const ids=new Set(cards.map((card)=>card.id));
const duplicateIds=cards.map((card)=>card.id).filter((id,index,all)=>all.indexOf(id)!==index);
assert.equal(ids.size,cards.length,`动态卡池 ID 不重复：${duplicateIds.join(",")}`);
assert(!ids.has("global_damage"),"旧弹道火控总成不再进入卡池");
for(const card of cards){assert(card.star>=1&&card.star<=6,`${card.id} 星级合法`);assert(card.max>=1&&card.max<=6,`${card.id} 等级上限合法`);}

const families={bullet:"弹道",laser:"激光",missile:"导弹",frost:"冰霜",arc:"电弧",support:"支援"};
for(const [turret,family] of Object.entries(families)){
  const basics=cards.filter((card)=>card.star===1&&card.tags.includes(family));
  assert(basics.length>=5,`${family} 至少五张一星基础卡`);
  for(const stat of turret==="support"?["range","base_rate","base_heal","base_crit","base_duration"]:["range","base_rate","base_damage","base_crit","base_crit_power"]){
    const id=stat==="range"?`${turret}_range`:`${turret}_${stat}`;
    assert(ids.has(id),`${family} 基础卡 ${id} 存在`);
    assert.equal(cards.find((card)=>card.id===id).max,5,`${id} 具有五级成长`);
  }
  assert(ids.has(`${turret}_active_skill`),`${family} 四星主动技能存在`);
  assert(ids.has(`${turret}_skill_cooldown`)&&ids.has(`${turret}_skill_power`),`${family} 五星主动技能分支存在`);
  for(let star=1;star<=6;star++)assert(cards.filter((card)=>card.star===star&&card.tags.includes(family)).length>=5,`${family} ★${star} 至少五种卡牌`);
}
for(const id of ["cryo_missile_echo","laser_arc_echo","bullet_support_echo","bullet_frost_echo","missile_arc_echo","support_laser_echo"]){const card=cards.find((item)=>item.id===id);assert.equal(card.star,6,`${id} 为六星连携`);}
for(const id of ["bullet_singularity_feed","laser_photon_memory","missile_recursive_swarm","frost_zero_archive","arc_storm_crown","support_nanite_covenant"]){const card=cards.find((item)=>item.id===id);assert(card?.selfApex&&card.star===6,`${id} 为对应炮塔的六星自成体系卡`);}
assert(ids.has("support_base_duration")&&!ids.has("support_base_crit_power"),"支援基础暴击治疗倍率已替换为机器人持续时间");
for(const card of cards.filter((item)=>item.star===1&&item.max===5&&item.passive?.values?.length===5)){const values=card.passive.values,previous=values[3],lastGain=values[4]-values[3],ratio=lastGain/Math.max(.0001,previous);assert(ratio>=.8&&ratio<=2,`${card.id} 第五级边际成长处于前四级累计的 80%–200%`);}
const minimumSpecialCards=[5,5,5,5,4,3];
for(let star=1;star<=6;star++)assert(cards.filter((card)=>card.star===star&&card.tags.includes("特殊")).length>=minimumSpecialCards[star-1],`特殊卡 ★${star} 满足当前规则族数量`);
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

const counts=Object.fromEntries(Object.entries(families).map(([key,tag])=>[key,cards.filter((card)=>card.tags.includes(tag)).length]));
const starCounts=Array.from({length:6},(_,index)=>cards.filter((card)=>card.star===index+1).length);
const specialStarCounts=Array.from({length:6},(_,index)=>cards.filter((card)=>card.star===index+1&&card.tags.includes("特殊")).length);
const fullRanks=new Map(cards.map((card)=>[card.id,card.max]));
const terminalProfiles=Object.fromEntries(Object.entries(families).map(([key,tag])=>{const profile=Balance.terminalSynergyProfile(cards,fullRanks,tag);return [key,{...profile,multiplier:+profile.multiplier.toFixed(2)}];}));
const terminalMultipliers=Object.fromEntries(Object.entries(terminalProfiles).map(([key,profile])=>[key,profile.multiplier]));
for(const [family,multiplier] of Object.entries(terminalMultipliers))assert(multiplier>=15&&multiplier<=40,`${family} 全卡终局乘区处于 15—40 倍目标区间`);
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
