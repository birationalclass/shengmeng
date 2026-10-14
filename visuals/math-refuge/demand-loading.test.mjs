import test from 'node:test';
import assert from 'node:assert/strict';
import {ResourceScheduler} from './resource-scheduler.js';
import {RuntimeTransfers} from './runtime-loading.js';
import {readFileSync} from 'node:fs';
const turns=()=>{const callbacks=[];let clock=0;return {callbacks,api:{performance:{now:()=>clock},setTimeout(fn){callbacks.push(fn);},requestIdleCallback(fn){callbacks.push(fn);}},async step(){callbacks.shift()?.();clock+=1;for(let i=0;i<8;i++)await Promise.resolve();}};};
test('optional work never starts during opening, even after many timer turns',async()=>{
 const h=turns(),p={entered:true,opening:true},s=new ResourceScheduler({policy:()=>p,api:h.api});let ran=false;
 const job=s.enqueue('upper','二楼',()=>ran=true);for(let i=0;i<25;i++)await h.step();assert.equal(ran,false);
 p.opening=false;for(let i=0;i<5;i++)await h.step();await job;assert.equal(ran,true);
});
test('entering is irrelevant to required and optional resource eligibility',async()=>{
 const h=turns(),p={entered:false,foreground:true,opening:false,moving:false},s=new ResourceScheduler({policy:()=>p,api:h.api});let built=0;
 const first=s.enqueue('clouds','云',()=>built++);for(let i=0;i<8;i++)await h.step();await first;assert.equal(built,1);
 p.entered=true;assert.equal(s.allowed({priority:3}),true);p.entered=false;assert.equal(s.allowed({priority:3}),true);
 p.moving=true;assert.equal(s.allowed({priority:3}),false);assert.equal(s.blockedBy({priority:3}),'镜头正在移动');p.moving=false;p.opening=true;assert.equal(s.blockedBy({priority:3}),'开场运镜保护');p.opening=false;p.foreground=false;assert.equal(s.blockedBy({priority:3}),'页面不可见');
});
test('movement and tab inactivity pause between individual interior batches',async()=>{
 const h=turns(),p={entered:true,opening:false,foreground:true},s=new ResourceScheduler({policy:()=>p,api:h.api}),built=[];
 const job=s.enqueue('classroom','教室',function*(){yield ()=>{built.push(1);p.moving=true;};yield ()=>built.push(2);});
 for(let i=0;i<10;i++)await h.step();assert.deepEqual(built,[1]);p.moving=false;p.foreground=false;for(let i=0;i<5;i++)await h.step();assert.deepEqual(built,[1]);
 p.foreground=true;for(let i=0;i<20;i++)await h.step();await job;assert.deepEqual(built,[1,2]);
});
test('required P0 textures can prepare before entry and each resource is built once',async()=>{
 const h=turns(),s=new ResourceScheduler({policy:()=>({entered:false,opening:true}),api:h.api});let count=0;
 const job=s.enqueue('water','海面',()=>count++,{priority:0});assert.equal(s.enqueue('water','海面',()=>count++,{priority:0}),job);for(let i=0;i<5;i++)await h.step();await job;assert.equal(count,1);
});
test('mandatory hall preparation cannot be starved by a renderer with no idle callbacks',async()=>{
 const s=new ResourceScheduler({policy:()=>({entered:true,opening:true}),api:{setTimeout,performance,requestIdleCallback(){assert.fail('required resources must not depend on idle frames');}}});let ran=false;
 await s.enqueue('hall','一楼材质',function*(){yield ()=>{ran=true;};},{priority:0});assert.equal(ran,true);
});
test('cache reads contribute resource size but contribute zero network speed',()=>{
 const m=new RuntimeTransfers('https://refuge.test/');const id=m.begin('https://refuge.test/test.png',1000,0);m.progress(id,1000,10);m.end(id);m.observe({name:'https://refuge.test/test.png',startTime:0,responseEnd:12,decodedBodySize:1000,transferSize:0},20);
 assert.equal(m.snapshot(20).speed,0);assert.equal(m.snapshot(20).total,1000);assert.equal(m.snapshot(20).last.cached,true);
});
test('compressed responses replace decoded streaming estimates without double counting',()=>{
 const m=new RuntimeTransfers('https://refuge.test/'),id=m.begin('https://refuge.test/test.json',null,0);m.progress(id,2000,10);m.end(id);m.observe({name:'https://refuge.test/test.json',startTime:0,responseEnd:20,decodedBodySize:2000,transferSize:600},20);
 assert.equal(m.snapshot(20).speed,300);assert.equal(m.snapshot(20).total,2000);assert.equal(m.snapshot(2100).speed,0);
});
test('failed and concurrent requests retain separate names and do not invent a total',()=>{
 const m=new RuntimeTransfers('https://refuge.test/'),a=m.begin('/a.json',null,0),b=m.begin('/b.png',500,0);m.progress(b,100,10);m.end(a,true);
 const value=m.snapshot(20);assert.equal(value.active.length,1);assert.equal(value.active[0].received,100);assert.equal(value.last.error,true);assert.equal(value.total,0);
});
test('late interiors use the migrated building coordinates for main hall and classroom',async()=>{
 const threeURL=new URL('../3d/vendor/three.module.js',import.meta.url).href,siteURL=new URL('./site-layout.js',import.meta.url).href;
 const plan=readFileSync(new URL('./campus-plan.js',import.meta.url),'utf8').match(/export const bridgePlan=(.*);/)[1];
 const source=readFileSync(new URL('./campus-layout.js',import.meta.url),'utf8').replace(/^import .*;\r?\n/gm,'');
 const module=await import('data:text/javascript;base64,'+Buffer.from(`import * as T from '${threeURL}';import {BUILDING_SCALE as S,HALL,LECTERN_SHAFT_PLAN} from '${siteURL}';const bridgePlan=${plan};\n`+source).toString('base64'));
 const T=await import(threeURL),S=Math.SQRT2;
 for(const [id,x,z] of [['01B',39,0],['07',-84,8]]){
  const scene=new T.Scene(),node=new T.Mesh(new T.BoxGeometry(1,1,1),new T.MeshBasicMaterial());node.position.set(x*S,3,z*S);scene.add(node);
  module.relocateArchitecture(scene,new Set([node]),false,{onlyId:id});const placed=scene.children.find(o=>o.visible&&o.userData.layoutId===id);assert.ok(placed);
  const expected=module.buildingOffset(id);assert.ok(Math.abs(placed.position.x-(x*S+expected.x))<1e-6);assert.ok(Math.abs(placed.position.z-(z*S+expected.z))<1e-6);
 }
});
