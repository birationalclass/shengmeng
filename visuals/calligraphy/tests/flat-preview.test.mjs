import fs from 'node:fs/promises';
import assert from 'node:assert/strict';
import test from 'node:test';
import {createTextGlyph} from '../engine/text-engine.js';
import {flatGlyph} from '../flat-preview.js';
import {prepareSpatialModel} from '../engine/spatial-model.js';
import {createVolume,updateVolume} from '../engine/surface.js';
const original=globalThis.fetch;
globalThis.fetch=async url=>String(url).startsWith('data/')?new Response(await fs.readFile(new URL('../'+url,import.meta.url))):original(url);

test('default running script preserves distinct components and authored motion',async()=>{
 const running=await createTextGlyph('孟晟'),cursive=await createTextGlyph('孟晟',{style:'cursive'});
 assert.equal(running.glyphStyle,'running');assert.equal(running.modeling.running,2);assert.equal(running.modeling.cursive,0);
 assert.ok(running.strokes.length>cursive.strokes.length);
 assert.ok(running.strokes.some(s=>s.name.includes('双竖'))&&running.strokes.some(s=>s.name.includes('日')));
 const model=prepareSpatialModel(running);assert.equal(model.report.brushPlan.inferredStrokes,0);
 for(const p of model.parts){const geometry=createVolume(50,24);for(const progress of [.0001,.3,.7,1]){updateVolume(geometry,p.spec,p.kind,progress,.27,'flow');assert.ok(geometry.attributes.position.array.every(Number.isFinite));}geometry.dispose();}
});
test('flat sample follows the selected geometry without changing its 3D source',async()=>{
 for(const [text,style] of [['孟','running'],['孟','cursive'],['孟','original'],['風天山','running'],['道法自然孟晟天山','running']]){
  const glyph=await createTextGlyph(text,{style}),before=JSON.stringify(glyph.strokes),flat=flatGlyph(glyph);
  assert.equal(flat.paths.length,glyph.strokes.length);assert.equal(JSON.stringify(glyph.strokes),before);
  assert.ok(flat.viewBox.every(Number.isFinite)&&flat.viewBox[2]>0&&flat.viewBox[3]>0);
  assert.ok(flat.paths.every(p=>/^M[-\d., L]+Z$/.test(p)&&!p.includes('NaN')));
 }
 const a=flatGlyph(await createTextGlyph('孟',{style:'running'})),b=flatGlyph(await createTextGlyph('孟',{style:'cursive'}));
 assert.notDeepEqual(a.paths,b.paths);assert.deepEqual(flatGlyph({text:'',strokes:[]}),{paths:[],viewBox:[0,0,1,1]});
});
