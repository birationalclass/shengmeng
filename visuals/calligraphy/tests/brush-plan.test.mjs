import fs from 'node:fs/promises';
import assert from 'node:assert/strict';
import test from 'node:test';
import crypto from 'node:crypto';
import {createTextGlyph} from '../engine/text-engine.js';
import {prepareSpatialModel} from '../engine/spatial-model.js';
import {createVolume,updateVolume} from '../engine/surface.js';
import {writingProgress} from '../engine/brush-gesture.js';
const original=globalThis.fetch;
globalThis.fetch=async url=>String(url).startsWith('data/')?new Response(await fs.readFile(new URL('../'+url,import.meta.url))):original(url);
const fixtures=JSON.parse(await fs.readFile(new URL('brush-baseline-hashes.json',import.meta.url),'utf8'));
const hash=a=>crypto.createHash('sha256').update(Buffer.from(a.buffer,a.byteOffset,a.byteLength)).digest('hex');
for(const text of ['風','孟晟','楊琪'])test(text+' preserves source and completed geometry',async()=>{
 const glyph=await createTextGlyph(text,{style:'original'}),before=fixtures[text],model=prepareSpatialModel(glyph);
 assert.equal(crypto.createHash('sha256').update(JSON.stringify(glyph.strokes)).digest('hex'),before.sourceHash);
 assert.equal(model.parts.length,before.parts.length);
 for(const [i,part] of model.parts.entries()){
  const geometry=createVolume(64,32);
  for(const p of [.45,1]){updateVolume(geometry,part.spec,part.kind,p,.27,'flow');if(p===1||text==='風')assert.equal(hash(geometry.attributes.position.array),before.parts[i].states[p].hash);}
  if(text==='風'){assert.equal(part.stroke.start,before.parts[i].start);assert.equal(part.stroke.end,before.parts[i].end);}
  geometry.dispose();
 }
 assert.equal(model.report.brushPlan.inferredStrokes,text==='風'?0:glyph.strokes.length);
});
test('inferred tips are smooth, finite and use lifted moves',async()=>{
 for(const text of ['永心之','山水','國龍']){
  const glyph=await createTextGlyph(text),model=prepareSpatialModel(glyph);assert.equal(model.report.brushPlan.inferredStrokes,glyph.strokes.length);
  for(const part of model.parts){let previous=-1;for(let k=0;k<=160;k++){const p=writingProgress(part.spec,k/160);assert.ok(p>=previous-1e-9&&p>=0&&p<=1);previous=p;}
   const geometry=createVolume(40,24);
   for(const p of [.00001,.08,.3,.5,.8,.98,1]){updateVolume(geometry,part.spec,part.kind,p,.27,'flow');assert.ok(geometry.attributes.position.array.every(Number.isFinite));}
   geometry.dispose();
  }
  assert.ok(model.report.brushPlan.lifts.every(l=>l.end>=l.start&&l.depositsInk===false));
 }
});
