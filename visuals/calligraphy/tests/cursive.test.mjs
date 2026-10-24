import fs from 'node:fs/promises';
import assert from 'node:assert/strict';
import test from 'node:test';
import {createTextGlyph} from '../engine/text-engine.js';
import {prepareSpatialModel} from '../engine/spatial-model.js';
import {sampleRailSection} from '../engine/yang-volume.js';
import {createVolume,updateVolume} from '../engine/surface.js';
import {writingProgress} from '../engine/brush-gesture.js';
const original=globalThis.fetch;
globalThis.fetch=async url=>String(url).startsWith('data/')?new Response(await fs.readFile(new URL('../'+url,import.meta.url))):original(url);

test('cursive letters have authored continuous surfaces and an original comparison',async()=>{
 const glyph=await createTextGlyph('孟晟'),prior=await createTextGlyph('孟晟',{style:'original'}),model=prepareSpatialModel(glyph);
 assert.equal(glyph.text,prior.text);assert.equal(glyph.modeling.cursive,2);
 assert.equal(prior.modeling.automatic,2);assert.equal(prior.modeling.cursive,0);
 assert.ok(model.parts.length<prior.strokes.length);
 const meng=model.parts.filter(p=>p.stroke.character===0);
 assert.equal(meng.length,1,'The whole 孟 is one surface, so its internal turns cannot have closing caps or restart times.');
 const spec=meng[0].spec,chord=sampleRailSection(spec,0).center.distanceTo(sampleRailSection(spec,1).center);
 assert.ok(spec.length>chord*3,'The path follows the character loops rather than joining two endpoints directly.');
 assert.equal(model.report.brushPlan.inferredStrokes,0);
 for(const part of model.parts){
  assert.ok(part.spec.brush&&part.spec.gesture&&!part.spec.gesture.inferred);
  let previous=-1;for(let k=0;k<=200;k++){const p=writingProgress(part.spec,k/200);assert.ok(p>=previous-1e-9);previous=p;}
  const geometry=createVolume(80,32);
  for(const p of [.00001,.06,.25,.45,.65,.85,1]){updateVolume(geometry,part.spec,part.kind,p,.27,'flow');assert.ok(geometry.attributes.position.array.every(Number.isFinite));}
  geometry.dispose();
 }
 const depth=Array.from({length:301},(_,i)=>sampleRailSection(meng[0].spec,i/300).center.z);
 assert.ok(Math.max(...depth)-Math.min(...depth)>.5,'The cursive loop travels through depth rather than remaining planar.');
});
test('style preserves code points and identifies fallback letters',async()=>{
 const glyph=await createTextGlyph('孟天晟山');
 assert.equal(glyph.text,'孟天晟山');assert.equal(glyph.modeling.cursive,2);assert.equal(glyph.modeling.automatic,1);
 assert.deepEqual(glyph.charSources.map(s=>s.cursive),[true,false,true,false]);
 for(const [i,s] of glyph.strokes.entries())if(i)assert.ok(s.start>=glyph.strokes[i-1].end-1e-8);
});
