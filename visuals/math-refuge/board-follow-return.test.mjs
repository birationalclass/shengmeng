import test from 'node:test';import assert from 'node:assert/strict';import vm from 'node:vm';import {readFileSync} from 'node:fs';import * as T from '../3d/vendor/three.module.js';
const source=readFileSync(new URL('./app.js',import.meta.url),'utf8'),start=source.indexOf('    if(!blend&&dt>0){'),end=source.indexOf('\n',start),step=source.slice(start,end);
test('forward/back-only manual translation returns continuously without snapping its target',()=>{
 const c={blend:null,dt:1/60,camera:{position:new T.Vector3(0,2,8),fov:57},controls:{target:new T.Vector3(0,2,3)},position:new T.Vector3(0,2,5),target:new T.Vector3(0,2,0),shotFov:57,THREE:T};
 vm.runInNewContext(step,c);assert(c.position.z>7.8&&c.position.z<8);assert(c.target.z>2.8&&c.target.z<3,'translated look target also eases back');assert(Math.abs((c.position.z-c.target.z)-5)<1e-10);
 for(let i=0;i<180;i++){c.camera.position.copy(c.position);c.controls.target.copy(c.target);c.position.set(0,2,5);c.target.set(0,2,0);vm.runInNewContext(step,c);}assert(Math.abs(c.position.z-5)<.01);assert(Math.abs(c.target.z)<.01);
});
