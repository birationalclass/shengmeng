import assert from 'node:assert/strict';
import {routeBridge} from './design-routing.js';
const a=['A','',0,0,0,0,20,20], b=['B','',0,0,100,0,20,20], c=['C','',0,0,50,0,20,40];
const t=performance.now();const p=routeBridge(a,b,[a,b,c]);assert.ok(p?.length>=4);assert.ok(p.some(n=>Math.abs(n[1])>=21));assert.equal(routeBridge(a,a,[a]),null);console.log('PASS obstacle route',p,'time',Math.round(performance.now()-t));
