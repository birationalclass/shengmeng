import test from 'node:test';import assert from 'node:assert/strict';import {erasingPlan,eraserPose,ERASER_HALF_WIDTH,ERASER_HALF_HEIGHT} from './chalk-motion.js';
test('real ink takes precedence over broad authoring boxes and leaves the blank middle untouched',()=>{
 const width=1536,height=640,data=new Uint8ClampedArray(width*height*4);const regions=[[100,70,400,103],[700,450,1190,482]];
 for(const [left,top,right,bottom]of regions)for(let y=top;y<=bottom;y++)for(let x=left;x<=right;x++)data[(y*width+x)*4+3]=255;
 const misleading=Object.assign([0,0,width,height],{strokePath:[[0,0],[1536,640]]}),plan=erasingPlan({width,height,data},[misleading]);assert(plan.duration>=6/1.3&&plan.duration<12);assert(plan.segments.filter(s=>s.contact).every(s=>s.a[1]<140||s.a[1]>420),'empty rows must not become contact sweeps');
 for(const [left,top,right,bottom]of regions)for(const x of [left,(left+right)/2,right])for(const y of [top,(top+bottom)/2,bottom]){let covered=false;for(let i=0;i<=Math.ceil(plan.total);i++){const p=eraserPose(i/Math.ceil(plan.total),width,height,plan);if(!p.contact)continue;const dx=x-p.x,dy=y-p.y,c=Math.cos(p.angle),s=Math.sin(p.angle);if(Math.abs(dx*c+dy*s)<=ERASER_HALF_WIDTH&&Math.abs(-dx*s+dy*c)<=ERASER_HALF_HEIGHT){covered=true;break;}}assert(covered,'edge ink remains at '+x+','+y);}
});
