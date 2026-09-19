// Pinned upstream dependencies and CC0 material assets; no private user content.
import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
const base=new URL('./',import.meta.url);
async function save(relative,url){
  const destination=new URL(relative,base);await fs.mkdir(path.dirname(fileURLToPath(destination)),{recursive:true});
  const response=await fetch(url);if(!response.ok)throw new Error(`${response.status}: ${url}`);
  const bytes=Buffer.from(await response.arrayBuffer());await fs.writeFile(destination,bytes);console.log(relative,bytes.length);return bytes.toString();
}
const visited=new Set();
async function addon(name){
  if(visited.has(name))return;visited.add(name);
  const code=await save('vendor/'+name,'https://cdn.jsdelivr.net/npm/three@0.180.0/examples/jsm/'+name);
  for(const match of code.matchAll(/from\s+['"](\.[^'"]+)['"]/g))await addon(path.posix.normalize(path.posix.join(path.posix.dirname(name),match[1])));
}
await Promise.all(['objects/Water.js','objects/Sky.js','geometries/RoundedBoxGeometry.js','postprocessing/EffectComposer.js','postprocessing/RenderPass.js','postprocessing/UnrealBloomPass.js','postprocessing/OutputPass.js'].map(addon));
await save('assets/waternormals.jpg','https://raw.githubusercontent.com/mrdoob/three.js/r180/examples/textures/waternormals.jpg');
const material=await(await fetch('https://api.polyhaven.com/files/wood_floor_deck')).json();
for(const [kind,name] of [['Diffuse','wood-color.jpg'],['Normal','wood-normal.jpg'],['Rough','wood-rough.jpg']]){
  const key=kind==='Normal' ? (material.nor_gl ? 'nor_gl' : Object.keys(material).find(k=>k.toLowerCase().includes('nor_gl'))) : Object.keys(material).find(k=>k.toLowerCase().startsWith(kind.toLowerCase()));
  if(!key)continue;
  const entry=material[key]['1k']?.jpg;if(entry)await save('assets/'+name,entry.url);
}
const marble=await(await fetch('https://api.polyhaven.com/files/marble_01')).json();
for(const [key,name] of [['Diffuse','stone-color.jpg'],['nor_gl','stone-normal.jpg'],['Rough','stone-rough.jpg']])await save('assets/'+name,marble[key]['1k'].jpg.url);
