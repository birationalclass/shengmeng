import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';
const source=readFileSync(new URL('./weather-sky.js',import.meta.url),'utf8');
test('disabled display cannot skip preparing cloud tiles, and movement pauses between tiles',async()=>{
 const events=[],mesh={userData:{}};let resume,blocked=false;
 const context={mesh,cloudVisibility:0,uniforms:{useVolumeClouds:{value:0}},setTimeout:fn=>queueMicrotask(fn),volumeClouds:{tileCount:3,async prepare(turn){await turn();events.push('compile');},setQuality:q=>events.push(q),update(){events.push('tile');if(events.filter(e=>e==='tile').length===1)blocked=true;}}};
 const start=source.indexOf('mesh.userData.prepareClouds='),end=source.indexOf('mesh.userData.beginArrivalFade=',start);
 vm.runInNewContext(source.slice(start,end),context);
 const job=mesh.userData.prepareClouds(()=>{},()=>blocked?new Promise(r=>resume=r):Promise.resolve(),'low');
 for(let i=0;i<20;i++)await Promise.resolve();assert.deepEqual(events,['compile','low','tile']);assert.equal(typeof resume,'function');blocked=false;resume();await job;assert.equal(events.filter(e=>e==='tile').length,3);
 const before=events.length;await mesh.userData.prepareClouds(()=>{},()=>assert.fail('off needs no GPU turn'),'off');assert.equal(events.length,before);
});
test('opening protection freezes precomputed clouds without disabling their visible texture',()=>{
 let atmosphereUpdates=0,cloudUpdates=0;const mesh={userData:{}},uniforms={};for(const key of ['sunPosition','cloud','atmosphereMap','atmosphereMapPrevious','atmosphereBlend','useAtmosphere','useVolumeClouds'])uniforms[key]={value:1};
 const context={mesh,uniforms,cloudsEnabled:true,cloudVisibility:1,resourceWorkAllowed:true,device:{},fadeToward:(a,b)=>b,atmosphere:{update(){atmosphereUpdates++;}},volumeClouds:{update(){cloudUpdates++;}}};
 const a=source.indexOf('mesh.userData.setResourceWorkAllowed='),b=source.indexOf('\n',a);vm.runInNewContext(source.slice(a,b),context);
 const start=source.indexOf('mesh.userData.updateAtmosphere='),end=source.indexOf('mesh.name=',start);vm.runInNewContext(source.slice(start,end),context);
 mesh.userData.setResourceWorkAllowed(false);mesh.userData.updateAtmosphere(.016);assert.equal(atmosphereUpdates,0);assert.equal(cloudUpdates,0);assert.equal(uniforms.useVolumeClouds.value,1);
 mesh.userData.setResourceWorkAllowed(true);mesh.userData.updateAtmosphere(.016);assert.equal(atmosphereUpdates,1);assert.equal(cloudUpdates,1);
});
