import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {SHOTS,smoothProgress,fadeAt,advanceShot} from './camera-paths.js';
import * as Three from '../3d/vendor/three.module.js';

test('five finite constant-path camera shots and bounded transitions',()=>{
  assert.equal(SHOTS.length,5);
  for(const shot of SHOTS){
    assert(shot.duration>=20);assert(shot.fov>30&&shot.fov<70);
    for(const points of [shot.positions,shot.targets]){
      const curve=new Three.CatmullRomCurve3(points.map(p=>new Three.Vector3(...p)));
      for(let i=0;i<=100;i++)assert(curve.getPointAt(smoothProgress(i/100)).toArray().every(Number.isFinite));
    }
  }
  assert.equal(fadeAt(0),1);assert.equal(fadeAt(.5),0);assert(Math.abs(fadeAt(1)-1)<1e-9);
  const wrap=advanceShot(4,25.98,.05,1);assert.equal(wrap.index,0);assert(wrap.time>=0&&wrap.time<.1);
  assert.deepEqual(advanceShot(0,1,-5,1),{index:0,time:1});
});

test('all page and JavaScript local asset references resolve',async()=>{
  const root=new URL('./',import.meta.url);
  for(const file of ['index.html','app.js','scene.js','camera-paths.js']){
    const code=await fs.readFile(new URL(file,root),'utf8');
    const links=file.endsWith('.html') ? [...code.matchAll(/(?:src|href)="([^"#]+)"/g)].map(m=>m[1]) : [...code.matchAll(/(?:from\s+|import\()['"](\.[^'"]+)['"]/g)].map(m=>m[1]);
    for(const link of links){if(link.startsWith('http'))continue;await fs.access(new URL(link.split('?')[0],root));}
  }
  for(const name of ['wood-color.jpg','wood-normal.jpg','wood-rough.jpg','stone-color.jpg','stone-normal.jpg','stone-rough.jpg','waternormals.jpg'])assert((await fs.stat(new URL('assets/'+name,root))).size>1000);
  async function scan(directory){
    for(const entry of await fs.readdir(directory,{withFileTypes:true})){
      const file=new URL(entry.name+(entry.isDirectory()?'/':''),directory);
      if(entry.isDirectory()){await scan(file);continue;}
      if(!entry.name.endsWith('.js'))continue;
      const code=(await fs.readFile(file,'utf8')).replace(/\/\*[\s\S]*?\*\//g,'');
      for(const match of code.matchAll(/from\s+['"]([^'"]+)['"]/g)){
        if(match[1]==='three')continue;
        const target=match[1].startsWith('three/addons/')?new URL(match[1].replace('three/addons/','vendor/'),root):new URL(match[1].split('?')[0],file);
        await fs.access(target);
      }
    }
  }
  await scan(root);
  const html=await fs.readFile(new URL('index.html',root),'utf8');
  const ids=new Set([...html.matchAll(/id="([^"]+)"/g)].map(m=>m[1]));
  const app=await fs.readFile(new URL('app.js',root),'utf8');
  for(const match of app.matchAll(/\$\('([^']+)'\)/g))assert(ids.has(match[1]),'Missing element '+match[1]);
});

test('scene assembly creates valid model buffers without a browser or GPU',async()=>{
  const coreURL=new URL('../3d/vendor/three.module.js',import.meta.url).href;
  const asModule=source=>'data:text/javascript;base64,'+Buffer.from(source).toString('base64');
  async function inlineAddon(file){return asModule((await fs.readFile(new URL(file,import.meta.url),'utf8')).replaceAll("from 'three'",`from '${coreURL}'`));}
  let source=await fs.readFile(new URL('./scene.js',import.meta.url),'utf8');
  source=source.replace("import * as THREE from 'three';",'const THREE=globalThis.__retreatTestThree;');
  for(const file of ['./vendor/geometries/RoundedBoxGeometry.js','./vendor/objects/Water.js','./vendor/objects/Sky.js'])source=source.replace(file,await inlineAddon(file));
  const calls=[];
  globalThis.__retreatTestThree={...Three,
    TextureLoader:class{async loadAsync(){const texture=new Three.Texture();texture.image={width:256,height:256};return texture;}},
    PMREMGenerator:class{fromScene(){return {texture:new Three.Texture(),dispose(){}};}dispose(){}}
  };
  globalThis.document={createElement:()=>({width:0,height:0,getContext:()=>({fillRect(){},fillText(text){calls.push(text);}})})};
  try{
    const {createRetreat}=await import(asModule(source));
    const scene=new Three.Scene();
    const result=await createRetreat({capabilities:{getMaxAnisotropy:()=>8}},scene,()=>{});
    assert(result.water.isMesh);assert(result.sculpture.isMesh);assert(scene.environment);
    let instances=0,triangles=0;
    for(const object of scene.children){
      if(!object.geometry)continue;
      assert([...object.geometry.attributes.position.array].every(Number.isFinite));
      if(object.isInstancedMesh){assert([...object.instanceMatrix.array].every(Number.isFinite));instances+=object.count;}
      triangles+=(object.geometry.index?.count || object.geometry.attributes.position.count)/3*(object.isInstancedMesh?object.count:1);
    }
    assert(instances>10000);assert(triangles<5000000);assert(calls.some(s=>s.includes('Hⁿ')));
    assert(result.water.material.uniforms.time);assert.equal(typeof result.lighting,'function');
    result.lighting(0,true);result.lighting(100,true);result.dispose();
    console.log(JSON.stringify({sceneObjects:scene.children.length,instances,triangles}));
  }finally{delete globalThis.__retreatTestThree;delete globalThis.document;}
});
