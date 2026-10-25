import assert from 'node:assert/strict';
import test from 'node:test';
import fs from 'node:fs/promises';
import {createTextGlyph} from '../engine/text-engine.js';
import {prepareSpatialModel} from '../engine/spatial-model.js';
import {createVolume,updateVolume} from '../engine/surface.js';
import {writingProgress} from '../engine/brush-gesture.js';
const original=globalThis.fetch;
globalThis.fetch=async url=>String(url).startsWith('data/')?new Response(await fs.readFile(new URL('../'+url,import.meta.url))):original(url);
test('02 builds volumetric animated characters with an identified supplement',async()=>{
 const glyph=await createTextGlyph('孟晟楊琪');assert.equal(glyph.glyphStyle,'kouzan');assert.equal(glyph.modeling.kouzan,4);assert.equal(glyph.modeling.supplements,1);
 assert.equal(glyph.charSources.find(s=>s.character==='琪').supplement,true);assert.match(glyph.charSources.find(s=>s.character==='琪').description,/原字体.*空字形/);
 const model=prepareSpatialModel(glyph);assert.equal(model.report.brushPlan.inferredStrokes,0);
 const geometry=createVolume(64,32);for(const part of model.parts){let previous=-1;for(let i=0;i<=150;i++){const p=writingProgress(part.spec,i/150);assert.ok(p>=previous-1e-9);previous=p;}
  for(const p of [.00001,.03,.2,.5,.8,.98,1]){updateVolume(geometry,part.spec,part.kind,p,.27,'flow');assert.ok(geometry.attributes.position.array.every(Number.isFinite),part.stroke.name+' finite mesh');}
 }geometry.dispose();
 for(const [i,s] of glyph.strokes.entries())if(i)assert.ok(s.start>=glyph.strokes[i-1].end-1e-9);
});
test('02 preserves script choices and reports characters with existing models',async()=>{
 const glyph=await createTextGlyph('杨楊風');assert.equal(glyph.text,'杨楊風');assert.deepEqual(glyph.charSources.map(s=>s.kouzan),[false,true,false]);
 const old=await createTextGlyph('楊琪',{style:'original'});assert.equal(old.modeling.kouzan,0);assert.equal(old.modeling.supplements,0);
});
