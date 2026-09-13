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
 if(fine.chosen){assert.ok(g[2]<.64&&g[1]<.16,'only smallest size class emits');assert.equal(all.chosen,1);assert.ok(fine.offset[0]>=0);assert.equal(fine.offset[1],0);assert.equal(fine.offset[2],0);}
 if(g[2]>=.64||g[1]>=.16){assert.equal(fine.chosen,0);assert.equal(fine.alpha,1);assert.ok(fine.offset.every(x=>x===0),'larger grains stay at the source');}
}
assert.ok(fineCount>0&&fineCount<allCount);assert.equal(offset(0,0,0,.1,.1,.1,.1,2,0,[1,0,0],true).chosen,0);
console.log(`PASS finest-only emission: ${fineCount} fine grains versus ${allCount} unrestricted; larger grains remain in place`);
