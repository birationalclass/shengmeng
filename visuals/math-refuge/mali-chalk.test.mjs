import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {ENGLISH_CHALK_STYLE,MATH_CHALK_STYLE,fitMaliGlyph,maliOperations} from './mali-chalk.js';
import {authoredContext} from './authored-chalk.js';

test('the selected font keeps its aspect and fits narrow formula and script slots',()=>{
 const glyph={bounds:[40,60,150,210]};
 for(const box of [{x:8,y:12,width:60,height:80},{x:1,y:3,width:8,height:45},{x:90,y:2,width:50,height:9}]){
  const f=fitMaliGlyph(glyph,box),[l,t,r,b]=glyph.bounds;
  assert(f.scale>0);assert(f.x+l*f.scale>=box.x-1e-8);assert(f.y+t*f.scale>=box.y-1e-8);
  assert(f.x+r*f.scale<=box.x+box.width+1e-8);assert(f.y+b*f.scale<=box.y+box.height+1e-8);
  assert(Math.abs((r-l)*f.scale/((b-t)*f.scale)-110/150)<1e-8);
 }
 assert.equal(ENGLISH_CHALK_STYLE,'mali-italic');assert.equal(MATH_CHALK_STYLE,'mali-italic');
});
test('drawing a cached formula twice gives each raster instance an independent identity and mapped bounds',()=>{
 const glyph={char:'p',fontSize:160,width:256,origin:[40,190],strokes:[{index:1,points:[[52,90],[62,155]],box:[45,80,30,90]}]},operations=maliOperations(glyph,10,50,42,'#eee9d5'),image={width:100,height:100,authoredOperations:operations};
 const ctx={font:'42px RefugeLatin',drawImage(){}};const recorder=authoredContext(ctx);
 recorder.ctx.drawImage(image,0,0,200,200);recorder.ctx.drawImage(image,250,0,100,100);
 const rows=recorder.rows([[0,0,500,250]]);assert.equal(rows.length,2);
 assert.notEqual(rows[0].strokeRaster.group,rows[1].strokeRaster.group);
 assert.equal(rows[0].strokeRaster.glyphRect[2],operations[0].strokeRaster.glyphRect[2]*2);
 assert.equal(rows[1].strokeRaster.glyphRect[0],operations[0].strokeRaster.glyphRect[0]+250);
 assert.equal(rows[0].letterSeconds,rows[1].letterSeconds);
});
test('glyph assets have valid contacts and unclipped original font bounds',()=>{
 const dir=new URL('./assets/chalk/mali-italic/',import.meta.url),files=readFileSync(new URL('./mali-chalk.js',import.meta.url),'utf8').match(/(?:latin|extended)-[a-f0-9]+\.json/g);
 const all=files.flatMap(f=>JSON.parse(readFileSync(new URL(f,dir),'utf8')).glyphs);
 assert(all.some(g=>g.char==='s'));assert(all.some(g=>g.char==='p'));
 for(const g of all){assert(g.paths.length>0);assert.equal(g.paths.length,g.pixelCounts.length);assert(g.pixelCounts.every(n=>n>0));assert(g.bounds[0]>=0&&g.bounds[2]<g.width&&g.bounds[3]<g.width);}
});
