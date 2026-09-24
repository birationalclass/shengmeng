import test from 'node:test';import assert from 'node:assert/strict';
import {TimePresentation} from './time-presentation.js';import{RetreatTime}from'./retreat-time.js';import{shanghaiHour}from'./solar-state.js';import{seaDepthAt,beachMask}from'./sea-depth.js';
test('seeking changes the solar hour only under full fade, then follows playback directly',()=>{const p=new TimePresentation(18);p.seek();for(let i=0;i<10;i++){assert.equal(p.update(6,.01),18);assert(p.opacity<1);}let changed=false;for(let i=0;i<40;i++){const prior=p.hour;p.update(6,.01);if(p.hour!==prior){assert.equal(p.opacity,1);changed=true;}}assert(changed);assert.equal(p.opacity,0);assert.equal(p.update(6.001,.016),6.001);assert.equal(p.update(.001,.016),.001);});
test('accelerated midnight advances astronomical date',()=>{const c=new RetreatTime(()=>new Date('2026-09-25T12:00:00Z'),shanghaiHour);c.previewAt(23.99);c.play(60);c.update(2);assert.equal(c.date.toISOString().slice(0,10),'2026-09-26');assert(c.hour<.1);});
test('east terrace beach is a continuous sand shelf and does not alter the western campus',()=>{assert.equal(beachMask(40,0),0);assert.equal(beachMask(90,0),0);assert(seaDepthAt(56,0)<0);assert(seaDepthAt(62,0)>.05&&seaDepthAt(62,0)<1);assert(seaDepthAt(74,0)>seaDepthAt(62,0));for(let x=52;x<90;x+=.01)assert(Math.abs(seaDepthAt(x+.01,0)-seaDepthAt(x,0))<.05);});

import{erasingPlan,eraserPose}from'./chalk-motion.js';
test('wide blackboard regions use broad bows with stable eraser angle',()=>{const p=erasingPlan(null,[[80,70,850,190]]);assert(p.segments.some(s=>s.contact&&Math.abs(s.curve)>=60));for(let t=0;t<=1;t+=.001){const q=eraserPose(t,1536,640,p);assert.equal(q.angle,-.19);assert(q.y>=0&&q.y<640);}});

test('sand reaches every terrace edge at deck height',()=>{for(const[x,z]of[[54,0],[24,0],[39,16.5],[39,-16.5]])assert(Math.abs(seaDepthAt(x,z)+.65*Math.SQRT2)<1e-8);});
