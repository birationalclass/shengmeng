import assert from 'node:assert/strict';
import test from 'node:test';
import fs from 'node:fs/promises';
import {createRequire} from 'node:module';
import {createTextGlyph,cleanText,loadCharacter} from '../engine/text-engine.js';
import {loadHomepageCharacter} from '../homepage-font.js';
import {paintHomepageGlyph} from '../font-volume.js';
import {prepareSpatialModel} from '../engine/spatial-model.js';
import {createVolume,updateVolume} from '../engine/surface.js';
import {flatGlyph} from '../flat-preview.js';
import {textPlacements,homepageQuote} from '../text-layout.js';
import {modelFiles} from '../engine/export-format.js';
const require=createRequire(import.meta.url),{createCanvas,Path2D}=require(process.env.CALLIGRAPHY_CANVAS_MODULE||'@napi-rs/canvas');
globalThis.fetch=async url=>new Response(await fs.readFile(new URL('../'+url,import.meta.url)));
const rasterizer=(g,n)=>{const c=createCanvas(n,n),ctx=c.getContext('2d');paintHomepageGlyph(ctx,g,n,Path2D);const bytes=ctx.getImageData(0,0,n,n).data;return Uint8Array.from({length:n*n},(_,i)=>bytes[i*4+3]);};
test('homepage quotation retains the actual ten title outlines and original column ratios',async()=>{
 assert.equal(cleanText(homepageQuote),homepageQuote);assert.throws(()=>cleanText(homepageQuote+'天之道损有余而'));
 const slots=textPlacements(10,'homepage');assert.equal(slots[0].x-slots[3].x,1.14*3.18);assert.equal(slots[0].y-slots[3].y,.43*3.18);assert.equal(slots[2].y,-2*3.18);assert.equal(slots[9].y,-6.43*3.18);
 const glyph=await createTextGlyph(homepageQuote,{style:'homepage',layout:'homepage',homepageOptions:{rasterizer,resolution:144}});
 assert.equal(glyph.text,homepageQuote);assert.equal(glyph.strokes.length,10);assert.equal(glyph.flatGlyphs.length,10);assert.ok(glyph.flatGlyphs.every(g=>g.font.titleOriginal));assert.ok(glyph.requiresHomepageLicense);
 assert.ok(glyph.duration>glyph.frontalAt&&glyph.frontalAt>glyph.writeEnd);assert.equal(flatGlyph(glyph).paths.length,10);
 for(const [i,s] of glyph.strokes.entries()){if(i)assert.ok(s.start>glyph.strokes[i-1].end);assert.ok(s.mesh.vertices.length>100);}
 const model=prepareSpatialModel(glyph);assert.equal(model.report.originalFont,true);
 for(const part of model.parts){const g=createVolume(0,0);updateVolume(g,part.spec,part.kind,1,.27);assert.ok(g.attributes.position.array.every(Number.isFinite));assert.ok(g.attributes.normal.array.every(Number.isFinite));assert.ok(g.boundingBox.max.z-g.boundingBox.min.z>.1);g.dispose();}
});
test('rounded font body is closed and grows monotonically as real mesh faces',async()=>{
 const glyph=await createTextGlyph('道',{style:'homepage',homepageOptions:{rasterizer,resolution:144}}),part=prepareSpatialModel(glyph).parts[0],g=createVolume(0,0);let prior=-1;
 for(const p of [.02,.12,.32,.55,.8,1]){updateVolume(g,part.spec,part.kind,p,.27);const v=g.attributes.position,index=g.index.array;let area=0;for(let j=0;j<g.userData.activeIndices;j+=3){const a=index[j],b=index[j+1],c=index[j+2];area+=Math.abs((v.getX(b)-v.getX(a))*(v.getY(c)-v.getY(a))-(v.getX(c)-v.getX(a))*(v.getY(b)-v.getY(a)));}assert.ok(area>=prior-1e-5);prior=area;}
 const edges=new Map(),index=g.index.array;for(let j=0;j<g.userData.activeIndices;j+=3)for(let k=0;k<3;k++){const a=index[j+k],b=index[j+(k+1)%3];if(a===b)continue;const key=Math.min(a,b)+':'+Math.max(a,b);edges.set(key,(edges.get(key)||0)+1);}
 const invalid=[...edges].filter(([,n])=>n!==2);assert.deepEqual(invalid.slice(0,5),[],'each completed surface edge must have two incident faces; invalid='+invalid.length);
 const obj=modelFiles([{g,i:0,mesh:{visible:true,position:{x:0,y:0,z:0}}}],{color:{r:.1,g:.1,b:.1},roughness:.3,metalness:.5},{} )['calligraphy.obj'];
 assert.equal((obj.match(/^v /gm)||[]).length,g.userData.activeVertices);assert.equal((obj.match(/^f /gm)||[]).length,g.userData.activeIndices/3);assert.ok(!obj.includes('NaN'));g.dispose();
 await assert.rejects(()=>loadHomepageCharacter('損'),/原字库没有/);
});
