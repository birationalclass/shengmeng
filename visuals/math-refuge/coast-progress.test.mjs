import assert from 'node:assert/strict';
import {fetchProgressBlob} from './resource-progress.js';
import {openingCoast,coastPath} from './opening-coast.js';
import {readFileSync} from 'node:fs';
const coast=openingCoast();
assert(coast.length>100);
for(let i=1;i<coast.length;i++){assert(coast[i].world[1]>coast[i-1].world[1],'north (-Z) to south (+Z)');assert(coast[i].screen[0]>coast[i-1].screen[0]);}
assert(Math.abs(coast[Math.floor(coast.length/2)].screen[1]-278)<4,'matches opening projection');
for(const headers of [{'content-length':'6'},{},{'content-length':'2','content-encoding':'gzip'}]){
 const values=[];const chunks=[new Uint8Array([1,2]),new Uint8Array([3,4,5,6])];
 const response=new Response(new ReadableStream({pull(controller){chunks.length?controller.enqueue(chunks.shift()):controller.close();}}),{headers});
 const blob=await fetchProgressBlob('test',p=>values.push(p),async()=>response);
 assert.equal(blob.size,6);assert.equal(values.at(-1),1);assert(values.every((v,i)=>v>=0&&v<=1&&(!i||v>=values[i-1])));
 if(headers['content-length']==='6')assert(values.length>2,'reports intermediate completed chunks');
 else assert.deepEqual(values,[1],'unknown or encoded sizes must not fake transfer progress');
}
await assert.rejects(fetchProgressBlob('test',()=>assert.fail('failure cannot report completion'),async()=>new Response('',{status:503})),/503/);
console.log('Coast projection, north-to-south ordering, byte progress and failure semantics passed.');