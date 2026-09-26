import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import * as T from '../3d/vendor/three.module.js';
const url=new URL('./boats.js',import.meta.url);
const source=(await readFile(url,'utf8')).replace(/from '([^']+)'/g,(_,path)=>`from '${new URL(path==='three'?'../3d/vendor/three.module.js':path,url).href}'`);
const {createBoats}=await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
test('sunrise boat travels left to right in 45 seconds, stays offshore and resets',()=>{
 const scene=new T.Scene(),fleet=createBoats(scene),boat=fleet.boats.find(b=>b.name==='Sunrise crossing sailboat'),other=fleet.boats.find(b=>b.name==='Auditorium east sailboat');
 const x=boat.position.x;fleet.update(.1);assert(Math.abs(boat.position.z+30)<1e-8);fleet.startSunrise();let previous=-30;
 for(let i=0;i<450;i++){fleet.update(.1);assert(boat.position.z>=previous);assert.equal(boat.position.x,x);assert(Math.hypot(boat.position.x-other.position.x,boat.position.z-other.position.z)>16);previous=boat.position.z;}
 assert(Math.abs(boat.position.z-22)<1e-8);fleet.update(.1);assert.equal(boat.position.z,22);fleet.resetSunrise();assert(Math.abs(boat.position.z+30)<1e-8);fleet.dispose();
});
