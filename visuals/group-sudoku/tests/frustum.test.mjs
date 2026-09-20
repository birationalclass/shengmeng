import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../../3d/vendor/three.module.js';
import {SudokuAtlas} from '../atlas.mjs';
test('far map corners survive maximum zoom and portrait overview without depth clipping',()=>{
 for(const [w,h] of [[1280,800],[390,844]]){
 const camera=new T.PerspectiveCamera(40,1,.65,260),fake={canvas:{clientWidth:w,clientHeight:h},renderer:{setSize(){}},camera};SudokuAtlas.prototype.resize.call(fake);
 assert.equal(camera.fov,40);assert.equal(camera.view.offsetY,-h*.04);
 for(const radius of [190,230,312])for(const phi of [.23,.8,1.45])for(let theta=0;theta<Math.PI*2;theta+=.3){camera.position.set(radius*Math.sin(phi)*Math.sin(theta),radius*Math.cos(phi),radius*Math.sin(phi)*Math.cos(theta));camera.lookAt(0,0,0);camera.updateMatrixWorld(true);for(const x of [-71,71])for(const z of [-73,73]){const p=new T.Vector3(x,-2,z).project(camera);assert.ok(p.z<1&&p.z>-1);}}
 }
});
