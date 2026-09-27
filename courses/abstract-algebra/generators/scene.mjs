import {contact} from './dynamics.mjs?v=orbit-glow-11';
const TAU=Math.PI*2;
export const valueSize=(score,max)=>.5+.5*Math.max(0,Math.min(1,score/Math.max(1,max)));
export class Scene {
 constructor(canvas,onPick){this.canvas=canvas;this.ctx=canvas.getContext('2d');this.nodes=[];this.active=null;this.time=0;this.enabled=true;this.scores=new Map();this.resize=new ResizeObserver(()=>this.measure());this.resize.observe(canvas);canvas.addEventListener('pointerup',e=>{if(!this.enabled)return;const box=canvas.getBoundingClientRect();const n=this.nodes.find(n=>Math.hypot(n.x-e.clientX+box.left,n.y-e.clientY+box.top)<this.radius*this.scale(n)+7);if(n)onPick(n.id);});this.measure();}
 measure(){const box=this.canvas.getBoundingClientRect();this.w=box.width;this.h=box.height;const d=Math.min(devicePixelRatio||1,2);this.canvas.width=this.w*d;this.canvas.height=this.h*d;this.ctx.setTransform(d,0,0,d,0,0);this.radius=this.targetRadius();}
 targetRadius(){const count=this.group?.labels.length>16?(this.present?.size||2):(this.nodes.length||6);return Math.max(7,Math.min(48,this.w/14,this.h/11,Math.sqrt(this.w*this.h/count)*.15));}
 reset(group,seeds){this.group=group;this.seeds=new Set(seeds);this.present=new Set(seeds);this.active=null;this.nodes=group.labels.map((_,id)=>{const a=TAU*id/group.labels.length;return {id,x:this.w/2+Math.cos(a)*this.w*.32,y:this.h*.56+Math.sin(a)*this.h*.25,vx:Math.cos(a+1)*30,vy:Math.sin(a+1)*30,valueSize:1,orbitBand:.94,noise:Math.random()*TAU};});this.measure();}
 growth(n){const t=n.born===undefined?1:Math.min(1,Math.max(0,(this.time-n.born)/3.2));return .035+.965*t*t*(3-2*t);}
 scale(n){return this.growth(n)*(n.valueSize??1);}
 selection(seeds){this.seeds=new Set(seeds);this.present=new Set(seeds);}
 orbit(){const r=this.radius,top=r+Math.min(130,this.h*.26),bottom=Math.max(top+2*r,this.h-r-25);return {x:this.w/2,y:(top+bottom)/2,rx:Math.max(r*2,this.w/2-r-22),ry:Math.max(r,(bottom-top)/2),max:Math.max(1,...this.scores.values())};}
 start(op){this.active={...op,elapsed:0,hit:false};}
 tick(dt,advance,visualDt=dt){const op=this.active;for(const n of this.nodes){const target=op&&!op.hit&&(n.id===op.a||n.id===op.b)?1:0;n.highlight=Math.max(0,Math.min(1,(n.highlight||0)+(target?visualDt:-visualDt)));}let finished=null;for(let elapsed=0;elapsed<dt;){const step=Math.min(1/120,dt-elapsed);elapsed+=step;const event=this.integrate(step,advance);if(event)finished=event;}return finished;}
 integrate(dt,advance){this.time+=dt;this.radius+=(this.targetRadius()-this.radius)*Math.min(1,dt*.8);const op=this.active;if(op&&advance)op.elapsed+=dt;const live=this.nodes.filter(n=>(this.enabled&&this.nodes.length<=16)||this.present.has(n.id)),max=Math.max(1,...this.scores.values()),r=this.radius;
  const orbit=this.orbit();
  for(const n of live)n.valueSize+=(valueSize(this.scores.get(n.id)||0,max)-n.valueSize)*(1-Math.exp(-dt*1.6));
  for(const n of live){if(n.parent!==undefined)continue;const dx=n.x-orbit.x,dy=n.y-orbit.y,d=Math.hypot(dx,dy)||1,score=this.scores.get(n.id)||0,q=Math.max(.025,Math.hypot(dx/orbit.rx,dy/orbit.ry));const targetBand=.94-.58*score/orbit.max;n.orbitBand+=(targetBand-n.orbitBand)*(1-Math.exp(-dt*.22));const band=n.orbitBand;
   const radial=(n.vx*dx+n.vy*dy)/d,settle=(n.release||0)>this.time?.12:1;
   let ax=settle*((dx*(band/q-1))*1.8-radial*dx/d*2.8)-dy/d*14+Math.sin(this.time*.8+n.noise)*3,ay=settle*((dy*(band/q-1))*1.8-radial*dy/d*2.8)+dx/d*14+Math.cos(this.time*.7+n.noise)*3;
   if(op&&!op.hit&&op.a!==op.b&&(n.id===op.a||n.id===op.b)){const other=this.nodes[n.id===op.a?op.b:op.a];const ddx=other.x-n.x,ddy=other.y-n.y,dist=Math.hypot(ddx,ddy)||1;const desired=Math.min(100,Math.max(42,dist*.65));ax=(ddx/dist*desired-n.vx)*2.3;ay=(ddy/dist*desired-n.vy)*2.3;}
   n.vx+=ax*dt;n.vy+=ay*dt;const damp=Math.exp(-.12*dt);n.vx*=damp;n.vy*=damp;n.x+=n.vx*dt;n.y+=n.vy*dt;
   const top=r+Math.min(130,this.h*.26),bottom=Math.max(top+2*r,this.h-r-25);if(n.x<r+8){n.x=r+8;n.vx=Math.abs(n.vx);}if(n.x>this.w-r-8){n.x=this.w-r-8;n.vx=-Math.abs(n.vx);}if(n.y<top){n.y=top;n.vy=Math.abs(n.vy);}if(n.y>bottom){n.y=bottom;n.vy=-Math.abs(n.vy);}
  }
  for(let i=0;i<live.length;i++)for(let j=i+1;j<live.length;j++){const a=live[i],b=live[j];if(a.parent!==undefined||b.parent!==undefined)continue;const hit=contact(a,b,r*(this.scale(a)+this.scale(b))/2);if(hit){a.release=this.time+.5;b.release=this.time+.5;}if(hit&&advance&&op&&!op.hit&&((a.id===op.a&&b.id===op.b)||(a.id===op.b&&b.id===op.a)))this.birth(op,(a.x+b.x)/2,(a.y+b.y)/2);}
  if(advance&&op&&!op.hit&&op.a===op.b&&op.elapsed>1.2&&this.nodes[op.a].parent===undefined){const a=this.nodes[op.a];this.birth(op,a.x,a.y);}
  for(const child of live.filter(n=>n.parent!==undefined).sort((a,b)=>a.born-b.born)){const parent=this.nodes[child.parent],t=Math.min(1,(this.time-child.born)/3.2),scale=.035+.965*t*t*(3-2*t),distance=r*this.scale(parent)+r*this.scale(child)*.98;child.x=parent.x+Math.cos(child.budAngle)*distance;child.y=parent.y+Math.sin(child.budAngle)*distance;child.vx=parent.vx;child.vy=parent.vy;if(scale>=1/3){child.vx+=Math.cos(child.budAngle)*18;child.vy+=Math.sin(child.budAngle)*18;delete child.parent;}}
  if(op&&op.hit&&op.elapsed>2.8&&this.nodes.every(n=>!this.present.has(n.id)||n.born===undefined||this.time-n.born>=3.2)){this.active=null;return op;}return null;
 }
 birth(op,x,y){op.hit=true;op.elapsed=1.7;op.x=x;op.y=y;if(op.fresh){const n=this.nodes[op.c];n.x=x;n.y=y;n.vx=0;n.vy=0;n.born=this.time;if(op.a===op.b){n.parent=op.a;const parent=this.nodes[op.a];n.budAngle=Math.atan2(this.h*.55-parent.y,this.w/2-parent.x);n.x=parent.x+Math.cos(n.budAngle)*this.radius*this.scale(parent);n.y=parent.y+Math.sin(n.budAngle)*this.radius*this.scale(parent);}this.present.add(op.c);}this.onBirth?.(op);}
  draw(){
    const ctx=this.ctx,w=this.w,h=this.h,r=this.radius,op=this.active;ctx.clearRect(0,0,w,h);
    // An understated orbital field, drawn in CSS pixels on every display density.
    const glow=ctx.createRadialGradient(w/2,h*.56,10,w/2,h*.56,Math.min(w*.5,h*.48));glow.addColorStop(0,'#b1914420');glow.addColorStop(1,'#b1914400');ctx.fillStyle=glow;ctx.fillRect(0,0,w,h);
    const orbit=this.orbit();ctx.lineWidth=1;
    for(let score=0;score<=orbit.max;score+=Math.max(1,Math.ceil(orbit.max/5))){const band=.94-.58*score/orbit.max;ctx.strokeStyle=score===0?'#d4b97925':'#d4b97918';ctx.beginPath();ctx.ellipse(orbit.x,orbit.y,orbit.rx*band,orbit.ry*band,0,0,TAU);ctx.stroke();ctx.fillStyle='#c6ad7666';ctx.font='10px system-ui';ctx.textAlign='center';ctx.fillText('✦ '+score,orbit.x+orbit.rx*band-14,orbit.y-7);}
    if(op&&op.a!==op.b&&!op.hit){const a=this.nodes[op.a],b=this.nodes[op.b];ctx.strokeStyle='#e2c58788';ctx.setLineDash([3,7]);ctx.beginPath();ctx.moveTo(a.x,a.y);ctx.lineTo(b.x,b.y);ctx.stroke();ctx.setLineDash([]);}
    if(op&&op.hit&&op.elapsed<2.7){const age=op.elapsed-1.7;ctx.save();ctx.globalAlpha=Math.max(0,1-age);ctx.fillStyle='#e9cb89';for(let k=0;k<18;k++){const angle=k*2.4;const dist=age*(25+k*5);ctx.beginPath();ctx.arc(op.x+Math.cos(angle)*dist,op.y+Math.sin(angle)*dist,1+(k%3)*.35,0,TAU);ctx.fill();}ctx.restore();}
    for(const n of this.nodes){const present=this.present.has(n.id);if(!present&&(!this.enabled||this.nodes.length>16))continue;const selected=this.seeds.has(n.id),active=op&&(n.id===op.a||n.id===op.b),result=op&&op.hit&&n.id===op.c;const scale=this.scale(n),phase=n.highlight||0,light=phase*phase*(3-2*phase);ctx.save();ctx.translate(n.x,n.y);ctx.scale(scale,scale);ctx.globalAlpha=present?(this.enabled?1:.38+.62*light):.3;
      const color=selected?'#e7c786':'#a9d7c0';
      ctx.shadowColor=color;ctx.shadowBlur=20*light;const fill=ctx.createRadialGradient(-r*.3,-r*.4,0,0,0,r);fill.addColorStop(0,present?(selected?'#d1ac586b':'#88b59c66'):'#514a3020');fill.addColorStop(.75,'#24251c88');fill.addColorStop(1,present?'#dec27855':'#514a3020');ctx.fillStyle=fill;ctx.beginPath();ctx.arc(0,0,r,0,TAU);ctx.fill();ctx.shadowBlur=0;ctx.lineWidth=present?1.2+light:.8;ctx.strokeStyle=present?color:'#d0b36f';ctx.stroke();
      ctx.strokeStyle=present?'#fff3cc65':'#fff3cc20';ctx.beginPath();ctx.arc(0,0,r-4,3.7,4.95);ctx.stroke();ctx.fillStyle=present?'#f4ebd6':'#c7baa0';ctx.font=`${Math.max(10,Math.round(r*.73))}px Georgia`;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText(String(n.id+1),0,-5);ctx.font='10px system-ui';ctx.fillStyle='#d5b979';ctx.fillText('✦ '+(this.scores.get(n.id)||0),0,r*.46);ctx.font='12px Georgia';ctx.fillStyle=present?'#cfc5ab':'#a99b78';if(this.nodes.length<=24||active)ctx.fillText(this.group.labels[n.id],0,r+17);
      if(active&&op.a!==op.b){ctx.font='10px system-ui';ctx.fillStyle='#e7c786';ctx.fillText(n.id===op.a?'A':'B',0,-r-14);}
      if(result){ctx.globalAlpha*=Math.max(0,1-(op.elapsed-1.7)/1.8);ctx.beginPath();ctx.arc(0,0,r+8+(op.elapsed-1.7)*14,0,TAU);ctx.strokeStyle=color;ctx.stroke();}ctx.restore();
    }
  }
}
