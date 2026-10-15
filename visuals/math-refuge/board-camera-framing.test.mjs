import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../3d/vendor/three.module.js';
import {boardCameraFrame,stepBoardCameraZoom} from './board-camera-framing.js';
import {BOARD_LAYOUT} from './lecture-state.js';
import {configureLectureRoot} from './site-layout.js';
test('plus pulls back, minus approaches and repeated adjustments stop at both framing limits',()=>{
 let zoom=0;for(let i=0;i<20;i++)zoom=stepBoardCameraZoom(zoom,1);assert.equal(zoom,1);
 for(let i=0;i<20;i++)zoom=stepBoardCameraZoom(zoom,-1);assert.equal(zoom,0);
 assert.equal(stepBoardCameraZoom(.5,1),.6);assert.equal(stepBoardCameraZoom(.5,-1),.4);
});
test('every zoom step fits the complete current board and controls, and maximum fits all six boards',()=>{
 for(const aspect of [390/844,1,1280/720,2388/800])for(const column of [0,1,2])for(const boardY of [BOARD_LAYOUT.low,BOARD_LAYOUT.high]){
  let distance=0;
  for(let step=0;step<=10;step++){
   const frame=boardCameraFrame(aspect,57,step/10,{column,boardY});assert(frame.distance>=distance-1e-10);distance=frame.distance;
   const root=new T.Group();configureLectureRoot(root);root.updateMatrixWorld(true);
   const target=root.localToWorld(new T.Vector3(frame.x,frame.y,frame.z)),position=root.localToWorld(new T.Vector3(frame.x,frame.y,frame.z+frame.distance));
   const camera=new T.PerspectiveCamera(frame.fov,aspect,.01,1000);camera.position.copy(position);camera.lookAt(target);camera.updateMatrixWorld(true);
   const columns=step===10?[0,1,2]:[column],heights=step===10?[BOARD_LAYOUT.low,BOARD_LAYOUT.high]:[boardY];
   for(const col of columns)for(const y of heights)for(const x of [-2.65,2.65])for(const dy of [-1.025,1.025]){
    const p=root.localToWorld(new T.Vector3(22.4+5.6*col+x,y+dy,-10.78)).project(camera);assert(Math.abs(p.x)<1&&Math.abs(p.y)<1,'complete board stays within the rendered viewport');
   }
   for(const x of [-2.49,2.64]){const p=root.localToWorld(new T.Vector3(22.4+5.6*column+x,-.84,-11.302)).project(camera);assert(Math.abs(p.x)<1&&Math.abs(p.y)<1,'glass controls remain reachable');}
   if(step===10){assert.equal(frame.x,28);assert(Math.abs(frame.bounds.right-frame.bounds.left-16.8)<1e-10);assert(frame.distance<=14.041,'portrait overview stays inside the hall');}
  }
 }
});
