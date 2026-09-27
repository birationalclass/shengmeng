import assert from 'node:assert/strict';
import {RenderChangeGate} from './render-change-gate.js';
for(const hz of [30,60,120]){
 const g=new RenderChangeGate(),p=[0,2,0],q=[0,0,0,1];
 for(let i=0;i<hz*3;i++)g.sample(p,q,1/hz);assert(g.ready);
 g.sample(p,[0,.01,0,.99995],1/hz);assert(!g.ready,'rotation without translation blocks upgrades');
 for(let i=0;i<hz;i++)g.sample(p,q,1/hz);assert(!g.ready,'wait for two settled seconds');
 for(let i=0;i<hz*3;i++)g.sample(p,q,1/hz,true);assert(!g.ready,'opening and held keys keep adjustments deferred');
 for(let i=0;i<hz*3;i++)g.sample(p,q,1/hz);assert(g.ready);
 g.sample([.1,2,0],q,1/hz);assert(!g.ready,'crossing a doorway blocks upgrades');
}
console.log('PASS camera settlement gating at 30/60/120 Hz');
