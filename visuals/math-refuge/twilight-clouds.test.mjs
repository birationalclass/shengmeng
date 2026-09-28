import test from 'node:test';import assert from 'node:assert/strict';import {twilightCloudFactor as factor} from './twilight-clouds.js';
const near=(a,b)=>assert(Math.abs(a-b)<1e-12);
const events={sunrise:6,sunset:18};
test('both events reduce coverage to thirty percent and recover over symmetric half-hour windows',()=>{for(const event of [6,18]){near(factor(event,events),.3);near(factor(event-.25,events),.65);near(factor(event+.25,events),.65);near(factor(event-.5,events),1);near(factor(event+.5,events),1);}near(factor(12,events),1);});
test('continuous monotone falloff, midnight wrapping and absent solar events',()=>{let last=.3;for(let i=0;i<=500;i++){const x=factor(6+i/1000,events);assert(x>=last&&x<=1);last=x;}near(factor(23.75,{sunrise:0,sunset:12}),.65);near(factor(5,{sunrise:NaN,sunset:NaN}),1);});
