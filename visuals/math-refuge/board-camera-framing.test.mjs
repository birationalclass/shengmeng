import test from 'node:test';
import assert from 'node:assert/strict';
import * as T from '../3d/vendor/three.module.js';
import {boardCameraFrame,stepBoardCameraZoom} from './board-camera-framing.js';
import {BOARD_LAYOUT} from './lecture-state.js';
import {configureLectureRoot} from './site-layout.js';
import {BOARD_MOUNT_OFFSET} from './board-hardware.js';
import {TRAY_DOCK,trayControlLayout} from './board-tray-layout.js';
test('plus pulls back, minus approaches and repeated adjustments stop at both framing limits',()=>{
 let zoom=0;for(let i=0;i<20;i++)zoom=stepBoardCameraZoom(zoom,1);assert.equal(zoom,1);
 for(let i=0;i<20;i++)zoom=stepBoardCameraZoom(zoom,-1);assert.equal(zoom,0);
 assert.equal(stepBoardCameraZoom(.5,1),.6);assert.equal(stepBoardCameraZoom(.5,-1),.4);
});
test('current board stays centered and uncut at every zoom; nearest includes every tray control in all columns',()=>{
 for(const aspect of [390/844,1,1280/720,2388/800])for(const column of [0,1,2])for(const boardY of [BOARD_LAYOUT.low,BOARD_LAYOUT.high])for(const boardZ of [-10.45+BOARD_MOUNT_OFFSET,-10.29+BOARD_MOUNT_OFFSET]){
  let distance=0;
  for(let step=0;step<=10;step++){
   const frame=boardCameraFrame(aspect,57,step/10,{column,boardY,boardZ});assert(frame.distance>=distance-1e-10);distance=frame.distance;
   const root=new T.Group();configureLectureRoot(root);root.updateMatrixWorld(true);
   const target=root.localToWorld(new T.Vector3(frame.x,frame.y,frame.z)),position=root.localToWorld(new T.Vector3(frame.x,frame.y,frame.z+frame.distance));
   const camera=new T.PerspectiveCamera(frame.fov,aspect,.01,1000);camera.position.copy(position);camera.lookAt(target);camera.updateMatrixWorld(true);
   const center=root.localToWorld(new T.Vector3(22.4+column*5.6,boardY,boardZ)).project(camera);assert(Math.abs(center.x)<1e-10&&Math.abs(center.y)<1e-10,'board center is screen center');
   const columns=step===10?[0,1,2]:[column],heights=step===10?[BOARD_LAYOUT.low,BOARD_LAYOUT.high]:[boardY];let edge=0;
   for(const col of columns)for(const y of heights)for(const x of [-2.65-.04-.0025*Math.SQRT2,2.65+.04+.0025*Math.SQRT2])for(const dy of [-1.025-.04-.0025*Math.SQRT2,1.025+.04+.0025*Math.SQRT2]){
    const p=root.localToWorld(new T.Vector3(22.4+5.6*col+x,y+dy,(step===10?-10.29+BOARD_MOUNT_OFFSET:boardZ)+.0135)).project(camera);assert(Math.abs(p.x)<=1&&Math.abs(p.y)<=1,'complete outer frame stays within viewport');edge=Math.max(edge,Math.abs(p.x),Math.abs(p.y));
   }
   for(const slot of Object.values(trayControlLayout(column)).filter(p=>typeof p==='object'))for(const dx of [-slot.width/2,slot.width/2])for(const dy of [-slot.height/2,slot.height/2]){
    const p=root.localToWorld(new T.Vector3(slot.x+dx,slot.y+dy*Math.cos(TRAY_DOCK.tilt),slot.z-dy*Math.sin(TRAY_DOCK.tilt))).project(camera);
    assert(Math.abs(p.x)<1&&Math.abs(p.y)<1,'complete tray controls stay on screen');
   }
   if(step===10)assert(frame.distance<=14.4,'portrait overview stays inside the hall');
  }
 }
});
