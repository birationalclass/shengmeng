import test from 'node:test';import assert from 'node:assert/strict';import {cloudCoverageArea,coverageThreshold,excludedCloudArea} from './cloud-coverage.js';
const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
test('coverage includes all regions without sunrise or sunset exclusions',()=>{
 const area=cloudCoverageArea([[1,0],[-1,0]]);assert.equal(area.excluded,0);assert(area.eligible>0);assert.equal(area.total,area.eligible+area.excluded);assert.equal(area.samples.length,area.eligible);
 assert.equal(excludedCloudArea(30,0,[[1,0],[-1,0]]),0);assert.equal(excludedCloudArea(-30,0,[[1,0],[-1,0]]),0);assert.equal(excludedCloudArea(0,30,[[1,0],[-1,0]]),0);
 for(const wanted of [.1,.5,.83,1]){const threshold=coverageThreshold(area,wanted),actual=area.samples.reduce((n,v)=>n+smooth(threshold-.035,threshold+.035,v),0)/area.eligible;assert(Math.abs(actual-wanted)<.0001);}
});
