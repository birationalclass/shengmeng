import assert from 'node:assert/strict';
import test from 'node:test';
import {PLACES,THEMES,cameraSpline,stageTime,arrivalPhase,plaqueOffset} from '../journey.mjs';
test('eight round platforms do not overlap and bridges clear unrelated disks',()=>{
 assert.equal(PLACES.length,8);assert.equal(new Set(THEMES.map(t=>t.paper)).size,8);
 for(let i=0;i<8;i++)for(let j=i+1;j<8;j++)assert.ok(Math.hypot(PLACES[i][0]-PLACES[j][0],PLACES[i][1]-PLACES[j][1])>26.2);
 for(let i=0;i<7;i++){const a=PLACES[i],b=PLACES[i+1],d=b.map((v,k)=>v-a[k]),len=d[0]**2+d[1]**2;for(let j=0;j<8;j++){if(j===i||j===i+1)continue;const p=PLACES[j],u=Math.max(0,Math.min(1,((p[0]-a[0])*d[0]+(p[1]-a[1])*d[1])/len));assert.ok(Math.hypot(p[0]-a[0]-u*d[0],p[1]-a[1]-u*d[1])>14.5,`bridge ${i} intersects ${j}`);}}
});
test('cinematic interpolation has exact endpoints and continuous interior motion',()=>{
 const keys=[[0,[0,30,20],[0,0,0]],[2,[10,20,10],[10,0,0]],[7.3,[20,30,25],[20,0,0]]];
 assert.deepEqual(cameraSpline(keys,0),[keys[0][1],keys[0][2]]);assert.deepEqual(cameraSpline(keys,7.3),[keys[2][1],keys[2][2]]);
 for(let t=0;t<7.3;t+=.1)assert.ok(cameraSpline(keys,t).flat().every(Number.isFinite));
 const a=cameraSpline(keys,2-1e-5),b=cameraSpline(keys,2+1e-5);assert.ok(Math.abs(a[0][0]-b[0][0])<.001);assert.ok(Math.abs(stageTime.bridge+stageTime.flight-7.3)<1e-9);
});

test('construction starts only after the camera has stopped, and the board follows the buildings',()=>{assert.equal(arrivalPhase(2.7),'moving');assert.equal(arrivalPhase(2.9),'settled');assert.equal(arrivalPhase(3),'building');assert.equal(arrivalPhase(5),'building');assert.equal(arrivalPhase(5.2),'board');assert.equal(arrivalPhase(5.9),'ready');assert.equal(arrivalPhase(2.8,true),'ready');});

test('nameplates lie outside every disk',()=>{PLACES.forEach(([cx,cz],i)=>{const [x,z]=plaqueOffset(i);for(const [a,b]of PLACES)assert.ok(Math.hypot(Math.max(0,Math.abs(a-cx-x)-5.15),Math.max(0,Math.abs(b-cz-z)-1.13))>13.05);});});
