import test from 'node:test';import assert from 'node:assert/strict';import {erasingPlan,eraserPose} from './chalk-motion.js';import {ERASER_ANGLE,feltCoreBounds,feltContains} from './eraser-contact.js';
test('the eraser is upright then 15 degrees counterclockwise, with positive conservative core bounds',()=>{assert(Math.abs(-ERASER_ANGLE*180/Math.PI-105)<1e-10);const b=feltCoreBounds();assert(b.x>0&&b.y>b.x);for(const x of [-b.x,b.x])for(const y of [-b.y,b.y])assert(feltContains(x,y,{x:0,y:0,angle:ERASER_ANGLE},true));});
test('every actual ink pixel is covered by the opaque soft-felt core, including isolated edge strokes',()=>{
 const width=340,height=180,data=new Uint8ClampedArray(width*height*4),points=[];for(const [l,t,r,b]of [[0,0,4,8],[22,37,299,53],[70,116,330,138],[337,174,339,179]])for(let y=t;y<=b;y++)for(let x=l;x<=r;x++){data[(y*width+x)*4+3]=255;points.push([x,y]);}const plan=erasingPlan({width,height,data}),poses=Array.from({length:Math.ceil(plan.total)+1},(_,i)=>eraserPose(i/Math.ceil(plan.total),width,height,plan)).filter(p=>p.contact);for(const [x,y]of points)assert(poses.some(p=>feltContains(x,y,p,true)),'uncovered ink at '+x+','+y);
});

import {ERASER_SPEED,ERASER_TRANSFER_SPEED} from './chalk-motion.js';
test('contact and lifted sweeps run thirty percent faster',()=>{assert.equal(ERASER_SPEED/360,1.3);assert.equal(ERASER_TRANSFER_SPEED/720,1.3);});
