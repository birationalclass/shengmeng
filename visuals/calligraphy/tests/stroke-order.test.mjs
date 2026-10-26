import assert from 'node:assert/strict';
import test from 'node:test';
import fs from 'node:fs/promises';
import {createRequire} from 'node:module';
import {createTextGlyph,loadCharacter} from '../engine/text-engine.js';
import {paintHomepageGlyph,homepageDomain,homepagePad} from '../font-volume.js';
import {prepareSpatialModel} from '../engine/spatial-model.js';
import {createVolume,updateVolume} from '../engine/surface.js';
const require=createRequire(import.meta.url),{createCanvas,Path2D}=require(process.env.CALLIGRAPHY_CANVAS_MODULE||'@napi-rs/canvas');
globalThis.fetch=async url=>new Response(await fs.readFile(new URL('../'+url,import.meta.url)));
const rasterizer=(font,n)=>{const canvas=createCanvas(n,n),ctx=canvas.getContext('2d');paintHomepageGlyph(ctx,font,n,Path2D);const bytes=ctx.getImageData(0,0,n,n).data;return Uint8Array.from({length:n*n},(_,i)=>bytes[i*4+3]);};
const make=text=>createTextGlyph(text,{style:'homepage',homepageOptions:{rasterizer,resolution:260}});
function ownerAt(mesh,x,y){const {resolution:n,deposition}=mesh,cx=(x+homepagePad)/homepageDomain*n,cy=(y+homepagePad)/homepageDomain*n;let best=Infinity,id=-1;for(let yy=Math.max(0,Math.floor(cy)-4);yy<=Math.min(n-1,Math.ceil(cy)+4);yy++)for(let xx=Math.max(0,Math.floor(cx)-4);xx<=Math.min(n-1,Math.ceil(cx)+4);xx++){const k=yy*n+xx,d=(xx+.5-cx)**2+(yy+.5-cy)**2;if(deposition.mask[k]&&d<best){id=k;best=d;}}assert.ok(id>=0,'ink landmark '+x+','+y);return deposition.owner[id];}
function areaNear(g,x,y,r=30){const mx=(x-512)/1024*3.18,my=(512-y)/1024*3.18,radius=r/1024*3.18,p=g.attributes.position,ix=g.index.array;let area=0;for(let j=0;j<g.userData.activeIndices;j+=3){const [a,b,c]=[ix[j],ix[j+1],ix[j+2]],cx=(p.getX(a)+p.getX(b)+p.getX(c))/3,cy=(p.getY(a)+p.getY(b)+p.getY(c))/3;if(Math.abs(cx-mx)<radius&&Math.abs(cy-my)<radius)area+=Math.abs((p.getX(b)-p.getX(a))*(p.getY(c)-p.getY(a))-(p.getX(c)-p.getX(a))*(p.getY(b)-p.getY(a)));}return area;}
test('ten title characters have 66 matched strokes with ordered pen-down and lift intervals',async()=>{
 const glyph=await make('天之道损有余而补不足');let total=0;
 for(const [i,item] of glyph.strokes.entries()){
  const char=[...glyph.text][i],plan=item.mesh.strokePlan;assert.equal(plan.authored,true);assert.equal(plan.strokes.length,(await loadCharacter(char)).medians.length,char+' standard stroke count');assert.equal(plan.audit.unreachedPixels,0,char+' all ink is reached');
  for(const [j,s] of plan.strokes.entries()){assert.ok(s.start<s.drawEnd&&s.drawEnd<s.end);if(j)assert.ok(s.start>=plan.strokes[j-1].end);}
  total+=plan.strokes.length;
 }assert.equal(total,66);
 assert.deepEqual(glyph.strokes[0].mesh.strokePlan.strokes.map(s=>s.name),['横','横','撇','捺']);
 assert.deepEqual(glyph.strokes[1].mesh.strokePlan.strokes.map(s=>s.name),['点','横撇','捺']);
 assert.deepEqual(glyph.strokes[2].mesh.strokePlan.strokes.slice(-3).map(s=>s.name),['点','横折折撇','捺']);
});
test('recognizable terminals belong to their actual stroke, including the last tails and dots',async()=>{
 const landmarks={天:[[525,-85,0],[285,240,1],[235,470,2],[780,470,3]],之:[[540,-45,0],[590,100,1],[820,410,2]],道:[[415,255,4],[205,205,9],[270,350,10],[820,490,11]],损:[[350,470,1],[250,320,2],[810,480,9]],余:[[300,455,5],[685,415,6]],补:[[415,-135,0],[585,420,5],[830,245,6]],不:[[225,405,1],[480,380,2],[780,300,3]],足:[[180,400,5],[800,440,6]]};
 for(const [char,points] of Object.entries(landmarks)){const mesh=(await make(char)).strokes[0].mesh;for(const [x,y,want] of points)assert.equal(ownerAt(mesh,x,y),want,char+' at '+x+','+y);}
});
test('rendered Tian faces cannot expose its second horizontal, left fall or right fall early',async()=>{
 const glyph=await createTextGlyph('天',{style:'homepage',homepageOptions:{rasterizer,resolution:384}}),part=prepareSpatialModel(glyph).parts[0],g=createVolume(0,0),rois=[[525,-85],[285,240],[235,470],[780,470]];
 for(const [i,s] of part.spec.mesh.strokePlan.strokes.entries()){
  updateVolume(g,part.spec,part.kind,s.drawEnd+.8*(s.end-s.drawEnd),.27);
  for(let j=0;j<rois.length;j++){const area=areaNear(g,...rois[j]);if(j<=i)assert.ok(area>1e-5,'completed stroke '+(j+1)+' is present');else assert.ok(area<1e-9,'future stroke '+(j+1)+' must be absent');}
 }g.dispose();
});
