"use strict";

const assert=require("node:assert/strict");
const Balance=require("../balance-core.js");

function waveModel(wave){
  const early=Balance.earlyWaveProfile(wave),late=Balance.lateWaveProfile(wave);
  const count=Math.max(10,Math.floor((8+wave*2.35+Math.pow(wave,1.08))*early.countScale));
  const hp=36*Math.pow(1.15,wave-1)*(1+Math.max(0,wave-20)*.018)*early.hpScale*late.hpScale;
  const midBosses=wave<6?0:Math.min(3,1+Math.floor(Math.max(0,wave-6)/8)+(wave>=10&&wave%4===0?1:0));
  const hasFinalBoss=wave>=5,doubleBoss=wave>=10&&(wave%9===0||wave%13===0);
  const colossal=wave%3===0;
  const effectiveHp=count*hp*.98+midBosses*hp*6.35+(hasFinalBoss?hp*8.8*(1+wave*.04)*(colossal?1.35:1)*(doubleBoss?2:1):0);
  const attack=Math.pow(1.07,wave-1)*(1+Math.floor((wave-1)/5)*.07)*early.attackScale*late.attackScale;
  return {wave,count,hp:Math.round(hp),midBosses,doubleBoss,colossal,effectiveHp:Math.round(effectiveHp),attack:+attack.toFixed(2)};
}

function seeded(seed){let value=seed>>>0;return()=>{value=(value*1664525+1013904223)>>>0;return value/4294967296;};}
function simulate(seed=0x61ac71){
  const rng=seeded(seed);let power=7/2.4,draws=0,activeTowers=1,skillUptime=0;
  for(let opening=0;opening<8;opening++){const star=Balance.rollStar(Balance.BASE_STAR_PROBABILITIES,rng);draws+=1;power*=1+[.035,.065,.105,.16,.24,.38][star-1];if(star>=4)skillUptime+=.012*star;if(activeTowers<3&&rng()<.22)activeTowers+=1;}
  const rows=[];
  for(let wave=1;wave<=40;wave++){
    const probabilities=Balance.starProbabilities([Math.min(5,Math.floor(wave/6)),Math.min(5,Math.floor(wave/9)),Math.min(5,Math.floor(wave/12)),Math.min(5,Math.floor(wave/16)),Math.min(5,Math.floor(wave/21))]);
    const newCards=1+(wave>=4?1:0)+(wave%7===0?1:0);
    for(let draw=0;draw<newCards;draw++){const star=Balance.rollStar(probabilities,rng);draws+=1;power*=1+[.035,.065,.105,.16,.24,.38][star-1];if(star>=4)skillUptime+=.012*star;if(activeTowers<6&&rng()<.085+.012*wave)activeTowers+=1;}
    const model=waveModel(wave),coverage=1+Math.max(0,activeTowers-1)*.34,aoe=1+Math.max(0,activeTowers-2)*.11,active=1+Math.min(.48,skillUptime),estimatedDps=power*coverage*aoe*active,clearSeconds=model.effectiveHp/Math.max(1,estimatedDps);
    rows.push({...model,cards:draws,towers:activeTowers,dps:+estimatedDps.toFixed(1),clearSeconds:+clearSeconds.toFixed(1)});
  }
  return rows;
}

const runs=Array.from({length:200},(_,index)=>simulate(0x61ac71+index));
const checkpoints=[1,3,5,10,15,20,25,30,35,40].map((wave)=>{const values=runs.map((run)=>run[wave-1].clearSeconds).sort((a,b)=>a-b);const sample=runs[0][wave-1];return {wave,enemies:sample.count,hp:sample.hp,attack:sample.attack,p25:values[49],median:values[99],p75:values[149]};});
assert(checkpoints[0].median<75,"第一波不会因基础炮塔降档而拖成长局");
assert(checkpoints.find((row)=>row.wave===3).median>checkpoints.find((row)=>row.wave===1).median,"第三波巨型黑洞形成首个压力峰值");
assert(runs.every((run)=>run.every((row)=>Number.isFinite(row.clearSeconds)&&row.clearSeconds>0)),"模拟没有非法数值");
assert(waveModel(40).midBosses===3,"第 40 波固定提供三个中途小首领压力点");
assert(waveModel(40).hp>waveModel(30).hp*10,"30—40 波需要终局卡牌质变来跨越生命曲线");
console.log(JSON.stringify({runs:runs.length,checkpoints},null,2));
