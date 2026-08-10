"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const vm = require("node:vm");
const path = require("node:path");

const gamePath = path.join(__dirname,"..","game.js");
const source = fs.readFileSync(gamePath,"utf8");
const end = source.indexOf("  const CARD_MAP =");
assert(end > 0,"能定位动态卡牌目录");
const prefix = `${source.slice(0,end)}\n  globalThis.__cards=CARDS;\n})();`;
const canvas = {getContext:()=>({})};
const document = {querySelector:(selector)=>selector==="#gameCanvas"?canvas:{},querySelectorAll:()=>[]};
const sandbox = {console,document,window:{EndlessBalanceCore:{}},globalThis:null,Math,setTimeout,clearTimeout};
sandbox.globalThis=sandbox;
vm.runInNewContext(prefix,sandbox,{filename:"game-card-prefix.js"});
const cards=sandbox.__cards;
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
for(let star=1;star<=6;star++)assert(cards.filter((card)=>card.star===star&&card.tags.includes("特殊")).length>=5,`特殊卡 ★${star} 至少五种`);

const counts=Object.fromEntries(Object.entries(families).map(([key,tag])=>[key,cards.filter((card)=>card.tags.includes(tag)).length]));
const starCounts=Array.from({length:6},(_,index)=>cards.filter((card)=>card.star===index+1).length);
const specialStarCounts=Array.from({length:6},(_,index)=>cards.filter((card)=>card.star===index+1&&card.tags.includes("特殊")).length);
console.log(JSON.stringify({totalCards:cards.length,counts,starCounts,specialStarCounts},null,2));
