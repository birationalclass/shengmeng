import {contact} from './dynamics.mjs?v=motion-2';
const TAU=Math.PI*2;
export class Scene {
 constructor(canvas,onPick){this.canvas=canvas;this.ctx=canvas.getContext('2d');this.nodes=[];this.active=null;this.time=0;this.enabled=true;this.scores=new Map();this.resize=new ResizeObserver(()=>this.measure());this.resize.observe(canvas);canvas.addEventListener('pointerup',e=>{if(!this.enabled)return;const box=canvas.getBoundingClientRect();const n=this.nodes.find(n=>Math.hypot(n.x-e.clientX+box.left,n.y-e.clientY+box.top)<this.radius+7);if(n)onPick(n.id);});this.measure();}
 measure(){const box=this.canvas.getBoundingClientRect();this.w=box.width;this.h=box.height;const d=Math.min(devicePixelRatio||1,2);this.canvas.width=this.w*d;this.canvas.height=this.h*d;this.ctx.setTransform(d,0,0,d,0,0);this.radius=Math.max(13,Math.min(48,this.w/14,this.h/11,Math.sqrt(this.w*this.h/(this.nodes.length||6))*.15));}
 reset(group,seeds){this.group=group;this.seeds=new Set(seeds);this.present=new Set(seeds);this.active=null;this.nodes=group.labels.map((_,id)=>{const a=TAU*id/group.labels.length;return {id,x:this.w/2+Math.cos(a)*this.w*.32,y:this.h*.56+Math.sin(a)*this.h*.25,vx:Math.cos(a+1)*30,vy:Math.sin(a+1)*30,noise:Math.random()*TAU};});this.measure();}
 selection(seeds){this.seeds=new Set(seeds);this.present=new Set(seeds);}
 start(op){this.active={...op,elapsed:0,hit:false};}
 tick(dt,advance){let finished=null;for(let elapsed=0;elapsed<dt;){const step=Math.min(1/120,dt-elapsed);elapsed+=step;const event=this.integrate(step,advance);if(event)finished=event;}return finished;}
 integrate(dt,advance){this.time+=dt;const op=this.active;if(op&&advance)op.elapsed+=dt;const live=this.nodes.filter(n=>this.enabled||this.present.has(n.id)),max=Math.max(1,...this.scores.values()),r=this.radius;
  for(const n of live){const dx=n.x-this.w/2,dy=n.y-this.h*.55,d=Math.hypot(dx,dy)||1,score=this.scores.get(n.id)||0;const orbit=Math.min(this.w*.34,this.h*.32)*(1-.62*score/max);const pull=(orbit-d)*.6;
   let ax=dx/d*pull-dy/d*12+Math.sin(this.time*1.2+n.noise)*16,ay=dy/d*pull+dx/d*12+Math.cos(this.time*.9+n.noise)*16;
   if(op&&!op.hit&&op.a!==op.b&&(n.id===op.a||n.id===op.b)){const other=this.nodes[n.id===op.a?op.b:op.a];const ddx=other.x-n.x,ddy=other.y-n.y,dist=Math.hypot(ddx,ddy)||1;const desired=Math.min(100,Math.max(42,dist*.65));ax=(ddx/dist*desired-n.vx)*2.3;ay=(ddy/dist*desired-n.vy)*2.3;}
   n.vx+=ax*dt;n.vy+=ay*dt;const damp=Math.exp(-.12*dt);n.vx*=damp;n.vy*=damp;n.x+=n.vx*dt;n.y+=n.vy*dt;
   const top=r+Math.min(130,this.h*.26),bottom=Math.max(top+2*r,this.h-r-25);if(n.x<r+8){n.x=r+8;n.vx=Math.abs(n.vx);}if(n.x>this.w-r-8){n.x=this.w-r-8;n.vx=-Math.abs(n.vx);}if(n.y<top){n.y=top;n.vy=Math.abs(n.vy);}if(n.y>bottom){n.y=bottom;n.vy=-Math.abs(n.vy);}
  }
  for(let i=0;i<live.length;i++)for(let j=i+1;j<live.length;j++){const a=live[i],b=live[j];const hit=contact(a,b,r);if(hit&&advance&&op&&!op.hit&&((a.id===op.a&&b.id===op.b)||(a.id===op.b&&b.id===op.a)))this.birth(op,(a.x+b.x)/2,(a.y+b.y)/2);}
  if(advance&&op&&!op.hit&&op.a===op.b&&op.elapsed>1.2){const a=this.nodes[op.a];this.birth(op,a.x+r*1.5,a.y-r);}
  if(op&&op.hit&&op.elapsed>2.8){this.active=null;return op;}return null;
 }
 birth(op,x,y){op.hit=true;op.elapsed=1.7;op.x=x;op.y=y;if(op.fresh){const n=this.nodes[op.c];n.x=x;n.y=y;n.vx=0;n.vy=0;n.born=this.time;this.present.add(op.c);}this.onBirth?.(op);}
  draw(){
    const ctx=this.ctx,w=this.w,h=this.h,r=this.radius,op=this.active;ctx.clearRect(0,0,w,h);
    // An understated orbital field, drawn in CSS pixels on every display density.
    const glow=ctx.createRadialGradient(w/2,h*.56,10,w/2,h*.56,Math.min(w*.5,h*.48));glow.addColorStop(0,'#b1914420');glow.addColorStop(1,'#b1914400');ctx.fillStyle=glow;ctx.fillRect(0,0,w,h);
    ctx.strokeStyle='#c8aa6912';ctx.lineWidth=1;for(let k=0;k<3;k++){ctx.beginPath();ctx.ellipse(w/2,h*.56,w*(.21+k*.095),h*(.16+k*.065),-.12,0,TAU);ctx.stroke();}
    if(op&&op.a!==op.b&&!op.hit){const a=this.nodes[op.a],b=this.nodes[op.b];ctx.strokeStyle='#e2c58788';ctx.setLineDash([3,7]);ctx.beginPath();ctx.moveTo(a.x,a.y);ctx.lineTo(b.x,b.y);ctx.stroke();ctx.setLineDash([]);}
    if(op&&op.hit&&op.elapsed<2.7){const age=op.elapsed-1.7;ctx.save();ctx.globalAlpha=Math.max(0,1-age);ctx.fillStyle='#e9cb89';for(let k=0;k<18;k++){const angle=k*2.4;const dist=age*(25+k*5);ctx.beginPath();ctx.arc(op.x+Math.cos(angle)*dist,op.y+Math.sin(angle)*dist,1+(k%3)*.35,0,TAU);ctx.fill();}ctx.restore();}
    for(const n of this.nodes){const present=this.present.has(n.id);if(!present&&!this.enabled)continue;const selected=this.seeds.has(n.id),active=op&&(n.id===op.a||n.id===op.b),result=op&&op.hit&&n.id===op.c;let scale=n.born===undefined?1:Math.min(1,.2+(this.time-n.born)*2);ctx.save();ctx.translate(n.x,n.y);ctx.scale(scale,scale);ctx.globalAlpha=present?1:.4;
      const color=selected?'#e7c786':'#a9d7c0';
      if(active||result){ctx.shadowColor=color;ctx.shadowBlur=result?23:12;}const fill=ctx.createRadialGradient(-r*.3,-r*.4,0,0,0,r);fill.addColorStop(0,present?(selected?'#d1ac586b':'#88b59c66'):'#514a3020');fill.addColorStop(.75,'#24251c88');fill.addColorStop(1,present?'#dec27855':'#514a3020');ctx.fillStyle=fill;ctx.beginPath();ctx.arc(0,0,r,0,TAU);ctx.fill();ctx.shadowBlur=0;ctx.lineWidth=present?1.2:.8;ctx.strokeStyle=present?color:'#d0b36f';ctx.stroke();
      ctx.strokeStyle=present?'#fff3cc65':'#fff3cc20';ctx.beginPath();ctx.arc(0,0,r-4,3.7,4.95);ctx.stroke();ctx.fillStyle=present?'#f4ebd6':'#c7baa0';ctx.font=`${Math.round(r*.73)}px Georgia`;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText(String(n.id+1),0,-5);ctx.font='10px system-ui';ctx.fillStyle='#d5b979';ctx.fillText('✦ '+(this.scores.get(n.id)||0),0,r*.46);ctx.font='12px Georgia';ctx.fillStyle=present?'#cfc5ab':'#a99b78';ctx.fillText(this.group.labels[n.id],0,r+17);
      if(active&&op.a!==op.b){ctx.font='10px system-ui';ctx.fillStyle='#e7c786';ctx.fillText(n.id===op.a?'A':'B',0,-r-14);}
      if(result){ctx.globalAlpha*=Math.max(0,1-(op.elapsed-1.7)/1.8);ctx.beginPath();ctx.arc(0,0,r+8+(op.elapsed-1.7)*14,0,TAU);ctx.strokeStyle=color;ctx.stroke();}ctx.restore();
    }
  }
}
