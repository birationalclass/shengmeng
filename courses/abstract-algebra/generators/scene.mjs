import {collide} from './model.mjs';
const TAU=Math.PI*2, ease=t=>t*t*(3-2*t), mix=(a,b,t)=>a+(b-a)*t;
export class Scene {
  constructor(canvas,onPick){
    this.canvas=canvas;this.ctx=canvas.getContext('2d');this.nodes=[];this.active=null;this.time=0;this.onPick=onPick;this.enabled=true;
    this.resize=new ResizeObserver(()=>this.measure());this.resize.observe(canvas);
    canvas.addEventListener('pointerup',e=>{if(!this.enabled)return;const r=canvas.getBoundingClientRect(),x=e.clientX-r.left,y=e.clientY-r.top;const node=this.nodes.find(n=>Math.hypot(n.x-x,n.y-y)<this.radius+7);if(node)onPick(node.id);});
    this.measure();
  }
  measure(){const rect=this.canvas.getBoundingClientRect();this.w=rect.width;this.h=rect.height;const d=Math.min(devicePixelRatio||1,2);this.canvas.width=Math.round(this.w*d);this.canvas.height=Math.round(this.h*d);this.ctx.setTransform(d,0,0,d,0,0);this.radius=Math.max(18,Math.min(64,this.w/12,this.h/9));for(const n of this.nodes){n.x=Math.min(this.w-this.radius-10,Math.max(this.radius+10,n.x));n.y=Math.min(this.h-55,Math.max(150,n.y));}}
  reset(group,seeds){this.group=group;this.seeds=new Set(seeds);this.present=new Set(seeds);this.active=null;this.nodes=group.labels.map((_,id)=>{const angle=TAU*id/group.labels.length-Math.PI/2;return {id,x:this.w/2+Math.cos(angle)*this.w*.31,y:this.h*.58+Math.sin(angle)*this.h*.24,vx:Math.sin(id*2.7)*9,vy:Math.cos(id*3.1)*7};});}
  selection(seeds){this.seeds=new Set(seeds);this.present=new Set(seeds);}
  start(op){const a=this.nodes[op.a],b=this.nodes[op.b];this.active={...op,elapsed:0,a0:{x:a.x,y:a.y},b0:{x:b.x,y:b.y},hit:false};}
  tick(dt,advance){
    this.time+=dt;const op=this.active;
    if(op&&advance){op.elapsed+=dt;if(op.elapsed>=1.7&&!op.hit){op.hit=true;if(op.fresh)this.present.add(op.c);}}
    for(const n of this.nodes){
      if(op&&(n.id===op.a||n.id===op.b||n.id===op.c))continue;
      const angle=TAU*n.id/this.nodes.length-Math.PI/2;
      const homeX=this.w/2+Math.cos(angle)*this.w*.32+Math.sin(this.time*.4+n.id)*14,homeY=this.h*.6+Math.sin(angle)*this.h*.23+Math.cos(this.time*.35+n.id)*10;
      n.x+=(n.vx+(homeX-n.x)*1.3)*dt;n.y+=(n.vy+(homeY-n.y)*1.3)*dt;
      if(n.x<this.radius+12||n.x>this.w-this.radius-12)n.vx*=-1;
      if(n.y<160||n.y>this.h-65)n.vy*=-1;
      n.x=Math.max(this.radius+10,Math.min(this.w-this.radius-10,n.x));n.y=Math.max(150,Math.min(this.h-60,n.y));
    }
    if(op){this.position(op);if(op.elapsed>=3.5){this.active=null;return true;}}
    return false;
  }
  position(op){
    const a=this.nodes[op.a],b=this.nodes[op.b],c=this.nodes[op.c],r=this.radius,cx=this.w/2,cy=this.h*.57,t=op.elapsed;
    if(op.a===op.b){
      a.x=mix(op.a0.x,cx, ease(Math.min(1,t/.9)));a.y=mix(op.a0.y,cy,ease(Math.min(1,t/.9)));
      if(op.fresh&&t>=1.7){c.x=cx+(2*r+15)*ease(Math.min(1,(t-1.7)/1.1));c.y=cy-45*ease(Math.min(1,(t-1.7)/1.1));}
    }else{
      const start=cx-r*3.8,target=cx+r;
      if(t<.9){const q=ease(t/.9);a.x=mix(op.a0.x,start,q);a.y=mix(op.a0.y,cy,q);b.x=mix(op.b0.x,target,q);b.y=mix(op.b0.y,cy,q);}
      else if(t<1.7){a.x=mix(start,cx-r,(t-.9)/.8);a.y=cy;b.x=target;b.y=cy;}
      else {const velocity=collide({x:r*2.8/.8,y:0},{x:0,y:0},{x:1,y:0});a.x=cx-r+velocity[0].x*(t-1.7);a.y=cy;b.x=target+velocity[1].x*Math.min(t-1.7,.65);b.y=cy;if(op.fresh){c.x=cx;c.y=cy-2.6*r*ease(Math.min(1,(t-1.7)/.8));}}
    }
  }
  draw(){
    const ctx=this.ctx,w=this.w,h=this.h,r=this.radius,op=this.active;ctx.clearRect(0,0,w,h);
    // An understated orbital field, drawn in CSS pixels on every display density.
    const glow=ctx.createRadialGradient(w/2,h*.56,10,w/2,h*.56,Math.min(w*.5,h*.48));glow.addColorStop(0,'#b1914420');glow.addColorStop(1,'#b1914400');ctx.fillStyle=glow;ctx.fillRect(0,0,w,h);
    ctx.strokeStyle='#c8aa6912';ctx.lineWidth=1;for(let k=0;k<3;k++){ctx.beginPath();ctx.ellipse(w/2,h*.56,w*(.21+k*.095),h*(.16+k*.065),-.12,0,TAU);ctx.stroke();}
    if(op&&op.a!==op.b&&op.elapsed>.85&&op.elapsed<1.7){const a=this.nodes[op.a],b=this.nodes[op.b];ctx.strokeStyle='#e2c58788';ctx.setLineDash([3,7]);ctx.beginPath();ctx.moveTo(a.x+r,a.y);ctx.lineTo(b.x-r,b.y);ctx.stroke();ctx.setLineDash([]);ctx.beginPath();ctx.moveTo(b.x-r-9,b.y-5);ctx.lineTo(b.x-r,b.y);ctx.lineTo(b.x-r-9,b.y+5);ctx.stroke();}
    if(op&&op.hit&&op.elapsed<2.7){const age=op.elapsed-1.7;ctx.save();ctx.globalAlpha=Math.max(0,1-age);ctx.fillStyle='#e9cb89';for(let k=0;k<18;k++){const angle=k*2.4;const dist=age*(25+k*5);ctx.beginPath();ctx.arc(w/2+Math.cos(angle)*dist,h*.57+Math.sin(angle)*dist,1+(k%3)*.35,0,TAU);ctx.fill();}ctx.restore();}
    for(const n of this.nodes){const present=this.present.has(n.id);if(!present&&!this.enabled)continue;const selected=this.seeds.has(n.id),active=op&&(n.id===op.a||n.id===op.b),result=op&&op.hit&&n.id===op.c;let scale=1;if(result&&op.fresh)scale=Math.min(1,.15+(op.elapsed-1.7)*2);ctx.save();ctx.translate(n.x,n.y);ctx.scale(scale,scale);ctx.globalAlpha=present?1:.4;
      const color=selected?'#e7c786':'#a9d7c0';
      if(active||result){ctx.shadowColor=color;ctx.shadowBlur=result?23:12;}const fill=ctx.createRadialGradient(-r*.3,-r*.4,0,0,0,r);fill.addColorStop(0,present?(selected?'#d1ac586b':'#88b59c66'):'#514a3020');fill.addColorStop(.75,'#24251c88');fill.addColorStop(1,present?'#dec27855':'#514a3020');ctx.fillStyle=fill;ctx.beginPath();ctx.arc(0,0,r,0,TAU);ctx.fill();ctx.shadowBlur=0;ctx.lineWidth=present?1.2:.8;ctx.strokeStyle=present?color:'#d0b36f';ctx.stroke();
      ctx.strokeStyle=present?'#fff3cc65':'#fff3cc20';ctx.beginPath();ctx.arc(0,0,r-4,3.7,4.95);ctx.stroke();ctx.fillStyle=present?'#f4ebd6':'#c7baa0';ctx.font=`${Math.round(r*.73)}px Georgia`;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText(String(n.id+1),0,1);ctx.font='12px Georgia';ctx.fillStyle=present?'#cfc5ab':'#a99b78';ctx.fillText(this.group.labels[n.id],0,r+17);
      if(active&&op.a!==op.b){ctx.font='10px system-ui';ctx.fillStyle='#e7c786';ctx.fillText(n.id===op.a?'A →':'B',0,-r-14);}
      if(result){ctx.globalAlpha*=Math.max(0,1-(op.elapsed-1.7)/1.8);ctx.beginPath();ctx.arc(0,0,r+8+(op.elapsed-1.7)*14,0,TAU);ctx.strokeStyle=color;ctx.stroke();}ctx.restore();
    }
  }
}
