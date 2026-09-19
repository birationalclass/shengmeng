const assert=require('node:assert/strict');
const fs=require('node:fs');const vm=require('node:vm');const path=require('node:path');
const context={window:{}};vm.runInNewContext(fs.readFileSync(path.join(__dirname,'../opening-materials.js'),'utf8'),context);
const offset=context.window.CourseOpeningMaterials.radiationOffset;
let fineCount=0,allCount=0;
for(let i=0;i<10000;i++){
 const g=[(i*.61803398875)%1,(i*.41421356237)%1,(i*.73205080757)%1,(i*.23606797750)%1];
 const all=offset(0,0,0,...g,2,1,[1,0,0],false);
 const fine=offset(0,0,0,...g,2,1,[1,0,0],true);
 allCount+=all.chosen;fineCount+=fine.chosen;
 if(fine.chosen){assert.ok(g[2]<.64&&g[1]<.64,'fine-only seed population excludes coarse grains');assert.equal(all.chosen,1);assert.ok(fine.offset[0]>=0);assert.equal(fine.offset[1],0);assert.equal(fine.offset[2],0);}
 if(g[2]>=.64||g[1]>=.64){assert.equal(fine.chosen,0);assert.equal(fine.alpha,1);assert.ok(fine.offset.every(x=>x===0),'larger grains stay at the source');}
}
assert.ok(fineCount>0&&fineCount<allCount);assert.equal(offset(0,0,0,.1,.1,.1,.1,2,0,[1,0,0],true).chosen,0);
console.log(`PASS finest-only emission: ${fineCount} fine grains versus ${allCount} unrestricted; larger grains remain in place`);

for(const amount of [.1,.25,.45,.75,1]){
 let count=0;
 for(let i=0;i<10000;i++){
  const g=[(i*.61803398875)%1,(i*.41421356237)%1,(i*.73205080757)%1,(i*.23606797750)%1];
  count+=offset(0,0,0,...g,2,amount,[1,0,0],false).chosen;
 }
 assert.ok(Math.abs(count/10000-amount*.4)<.003,'the entire slider range emits twice the original 20% density');
}
console.log('PASS: doubled emission density at 10%, 25%, 45%, 75%, and 100% settings');

// Independent stratified seeds: quadrupling the selected micro-grain population
// must hold at every slider value, including the saved/default 45% setting.
for(const amount of [.01,.1,.25,.45,.75,1]){
 let before=0,after=0;
 for(let x=0;x<100;x++)for(let z=0;z<10;z++)for(let y=0;y<100;y++){
  const g=[(x+.5)/100,(y+.5)/100,(z+.5)/10,.31];
  const all=offset(0,0,0,...g,2,amount,[1,0,0],false);
  before+=all.chosen*(g[2]<.64&&g[1]<.16);
  const fine=offset(0,0,0,...g,2,amount,[1,0,0],true);after+=fine.chosen;
  if(fine.chosen){assert.deepEqual(fine.offset,all.offset);assert.equal(fine.alpha,all.alpha);}
 }
 assert(before>0);assert.equal(after,before*4,`4x count at ${amount}`);
}
console.log('PASS: fine-only count is exactly 4x at all tested settings; trajectories are unchanged');
