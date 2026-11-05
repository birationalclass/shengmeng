import {FACES, NORMALS, BASIS, compose, inverse} from './cube-model.mjs';

const PALETTE={U:'#eee5cd',R:'#b96854',F:'#759d8b',D:'#d8b775',L:'#d09263',B:'#668da9'};
const CORNERS=[[-1,1],[1,1],[1,-1],[-1,-1]];
const add=(a,b)=>a.map((v,i)=>v+b[i]);
const scale=(a,s)=>a.map(v=>v*s);
const ease=t=>t<.5?4*t*t*t:1-Math.pow(-2*t+2,3)/2;
const clamp=(v,a,b)=>Math.max(a,Math.min(b,v));
export function rotate(v,axis,a){
  const c=Math.cos(a),s=Math.sin(a),[x,y,z]=v;
  return axis===0?[x,c*y-s*z,s*y+c*z]:axis===1?[c*x+s*z,y,-s*x+c*z]:[c*x-s*y,s*x+c*y,z];
}
function polygon(ctx,points,r=.1){
  ctx.beginPath();points.forEach((p,i)=>{
    const prev=points[(i+points.length-1)%points.length],next=points[(i+1)%points.length];
    const a=[p[0]*(1-r)+prev[0]*r,p[1]*(1-r)+prev[1]*r],b=[p[0]*(1-r)+next[0]*r,p[1]*(1-r)+next[1]*r];
    if(i===0)ctx.moveTo(...a);else ctx.lineTo(...a);ctx.quadraticCurveTo(p[0],p[1],...b);
  });ctx.closePath();
}
function contains(p,vs){
  let inside=false;
  for(let i=0,j=vs.length-1;i<vs.length;j=i++){
    const a=vs[i],b=vs[j];
    if((a[1]>p[1])!==(b[1]>p[1])&&p[0]<(b[0]-a[0])*(p[1]-a[1])/(b[1]-a[1])+a[0])inside=!inside;
  }return inside;
}

/** A normalized 2–5 cube. The camera never changes the permutation. */
export class CubeView {
  constructor(canvas,model,{onMove=()=>{},onInspect=()=>{}}={}){
    this.canvas=canvas;this.ctx=canvas.getContext('2d');
    if(!this.ctx)throw new Error('此浏览器无法绘制魔方。');
    this.yaw=-.64;this.pitch=.46;this.zoom=1;this.labels=false;this.highlight=false;
    this.duration=350;this.moveSelection={depth:1,width:1};this.onMove=onMove;this.onInspect=onInspect;
    this.hit=[];this.surfaces=[];this.version=0;this.frame=0;this.resolve=null;this.animation=null;this.drag=null;this.disposed=false;
    this.listeners=[];
    const listen=(type,handler,options)=>{canvas.addEventListener(type,handler,options);this.listeners.push([type,handler,options]);};
    listen('contextmenu',e=>e.preventDefault());
    listen('pointerdown',e=>this.pointerDown(e));listen('pointermove',e=>this.pointerMove(e));listen('pointerup',e=>this.pointerUp(e));
    listen('pointercancel',()=>this.cancelDrag());listen('lostpointercapture',()=>this.cancelDrag());
    listen('wheel',e=>{e.preventDefault();this.zoom=clamp(this.zoom*Math.exp(-e.deltaY*.001),.65,1.8);this.draw();},{passive:false});
    this.resize=new ResizeObserver(()=>this.draw());this.resize.observe(canvas);
    this.setModel(model);
  }
  cancelTurn(){
    this.version++;if(this.frame)cancelAnimationFrame(this.frame);this.frame=0;
    this.animation=null;if(this.resolve){const done=this.resolve;this.resolve=null;done(false);}
  }
  setModel(model){
    this.cancelTurn();this.cancelDrag();this.model=model;this.state=model.identity();
    const m=model.size-1;this.locations=[];
    // Interior cubies become visible when an internal layer moves.
    for(let x=-m;x<=m;x+=2)for(let y=-m;y<=m;y+=2)for(let z=-m;z<=m;z+=2)this.locations.push([x,y,z]);
    this.moveSelection={depth:1,width:1};this.draw();
  }
  setState(p){
    if(p.length!==this.model.facelets.length)throw new RangeError('Permutation size does not match the displayed cube.');
    this.cancelTurn();this.state=Array.from(p);this.draw();
  }
  home(){this.yaw=-.64;this.pitch=.46;this.zoom=1;this.draw();}
  project(p){
    const v=rotate(rotate(p,1,this.yaw),0,this.pitch),k=7/(7-v[2]);
    return[this.w/2+v[0]*this.unit*k,this.h/2-v[1]*this.unit*k,v[2]];
  }
  viewNormal(n){return rotate(rotate(n,1,this.yaw),0,this.pitch);}
  transform(p,location){return this.animation&&this.animation.layers.has(location[this.animation.axis])?rotate(p,this.animation.axis,this.animation.angle):p;}
  normal(n,location){return this.transform(n,location);}
  draw(){
    if(this.disposed||!this.model)return;
    const rect=this.canvas.getBoundingClientRect();if(!rect.width||!rect.height)return;
    const dpr=Math.min(globalThis.devicePixelRatio||1,2.5);
    this.w=rect.width;this.h=rect.height;this.unit=Math.min(this.w/3.7,this.h/3.9)*this.zoom;
    const width=Math.round(this.w*dpr),height=Math.round(this.h*dpr);
    if(this.canvas.width!==width||this.canvas.height!==height){this.canvas.width=width;this.canvas.height=height;}
    const ctx=this.ctx;ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,this.w,this.h);
    ctx.save();ctx.translate(this.w/2,this.h/2+this.unit*1.35);ctx.scale(1,.2);
    const shadow=ctx.createRadialGradient(0,0,0,0,0,this.unit*1.5);shadow.addColorStop(0,'rgba(0,0,0,.38)');shadow.addColorStop(1,'rgba(0,0,0,0)');
    ctx.fillStyle=shadow;ctx.beginPath();ctx.arc(0,0,this.unit*1.5,0,Math.PI*2);ctx.fill();ctx.restore();
    const faces=[],n=this.model.size,at=inverse(this.state),half=.97/n,sticker=.84/n;
    for(const loc of this.locations){
      const center=scale(loc,1/n);
      for(const face of FACES){
        const normal=this.normal(NORMALS[face],loc),light=this.viewNormal(normal)[2];if(light<=.015)continue;
        const [r,u]=BASIS[face],centerFace=add(center,scale(NORMALS[face],half));
        const pts=CORNERS.map(([a,b])=>this.project(this.transform(add(centerFace,add(scale(r,a*half),scale(u,b*half))),loc)));
        faces.push({pts,z:pts.reduce((s,p)=>s+p[2],0)/4,body:true,light});
      }
    }
    this.model.facelets.forEach((s,i)=>{
      const normal=this.normal(s.n,s.p),light=this.viewNormal(normal)[2];if(light<=.015)return;
      const center=add(scale(s.p,1/n),scale(s.n,.985/n)),[r,u]=BASIS[s.face];
      const pts=CORNERS.map(([a,b])=>this.project(this.transform(add(center,add(scale(r,a*sticker),scale(u,b*sticker))),s.p)));
      const source=this.model.facelets[at[i]],isCentre=n%2===1&&s.row===(n-1)/2&&s.col===(n-1)/2;
      faces.push({pts,z:pts.reduce((a,p)=>a+p[2],0)/4,body:false,face:s.face,id:i,source:at[i],color:source.face,label:source.label,isCentre,moved:at[i]!==i,light,location:s.p,center:this.project(this.transform(center,s.p))});
    });
    faces.sort((a,b)=>a.z-b.z);this.surfaces=faces;this.hit=[];
    for(const f of faces){
      polygon(ctx,f.pts,f.body?.07:.11);
      if(f.body){
        ctx.fillStyle=`rgb(${22+f.light*10},${22+f.light*9},${20+f.light*7})`;ctx.fill();
        ctx.strokeStyle='rgba(220,197,142,.065)';ctx.lineWidth=.6;ctx.stroke();continue;
      }
      ctx.fillStyle=PALETTE[f.color];ctx.fill();ctx.save();ctx.clip();
      const g=ctx.createLinearGradient(f.pts[0][0],f.pts[0][1],f.pts[2][0],f.pts[2][1]);
      g.addColorStop(0,'rgba(255,246,215,.17)');g.addColorStop(.45,'rgba(255,255,255,0)');g.addColorStop(1,`rgba(0,0,0,${.15+(1-f.light)*.12})`);
      ctx.fillStyle=g;ctx.fill();ctx.restore();
      ctx.strokeStyle=this.highlight&&f.moved?'#fff0b7':'rgba(255,239,197,.23)';ctx.lineWidth=this.highlight&&f.moved?1.8:.7;ctx.stroke();
      if(this.highlight&&!f.moved){ctx.fillStyle='rgba(12,13,12,.50)';ctx.fill();}
      if(this.labels||f.isCentre){
        ctx.font=`400 ${Math.max(8,this.unit*(this.labels?.23:.30)/n)}px OpeningSans,Inter,Arial,sans-serif`;
        ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillStyle='rgba(18,22,20,.83)';
        ctx.fillText(this.labels?f.label:f.color,f.center[0],f.center[1]);
      }
      this.hit.push(f);
    }
  }
  turn(move){
    if(this.animation||this.resolve||this.disposed)return Promise.resolve(false);
    const info=this.model.moveInfo(move),permutation=this.model.movePermutation(move);
    const version=++this.version,duration=Math.max(0,Number(this.duration)||0)*(Math.abs(move.turns)===2?1.3:1),start=performance.now();
    return new Promise(resolve=>{
      this.resolve=resolve;
      const frame=now=>{
        if(this.version!==version||this.disposed)return;
        const t=duration?Math.min(1,(now-start)/duration):1;
        this.animation={axis:info.axis,layers:new Set(info.layers),angle:info.angle*move.turns*ease(t)};this.draw();
        if(t<1)this.frame=requestAnimationFrame(frame);
        else{
          this.frame=0;this.state=compose(this.state,permutation);this.animation=null;this.resolve=null;this.draw();resolve(true);
        }
      };this.frame=requestAnimationFrame(frame);
    });
  }
  point(e){const r=this.canvas.getBoundingClientRect();return[e.clientX-r.left,e.clientY-r.top];}
  pointerDown(e){
    if(this.drag||this.animation||(e.button!==0&&e.button!==2))return;
    const p=this.point(e),surface=[...this.surfaces].reverse().find(f=>contains(p,f.pts));
    const hit=surface&&!surface.body?surface:null;
    this.drag={p,last:p,hit:e.button===2||e.shiftKey?null:hit,moved:false,pointerId:e.pointerId};
    this.canvas.setPointerCapture(e.pointerId);this.canvas.classList.add('dragging');this.canvas.focus({preventScroll:true});e.preventDefault();
  }
  pointerMove(e){
    if(!this.drag||e.pointerId!==this.drag.pointerId)return;
    const p=this.point(e),d=this.drag,dx=p[0]-d.last[0],dy=p[1]-d.last[1];
    if(Math.hypot(p[0]-d.p[0],p[1]-d.p[1])>8)d.moved=true;
    if(!d.hit){this.yaw+=dx*.008;this.pitch=clamp(this.pitch+dy*.008,-1.4,1.4);this.draw();}
    d.last=p;
  }
  pointerUp(e){
    const d=this.drag;if(!d||e.pointerId!==d.pointerId)return;this.cancelDrag();
    if(!d.hit)return;if(!d.moved){this.onInspect(d.hit);return;}
    const p=this.point(e),dx=p[0]-d.p[0],dy=p[1]-d.p[1];
    const c=this.project(NORMALS[d.hit.face]),rx=d.p[0]-c[0],ry=d.p[1]-c[1],cross=rx*dy-ry*dx;
    const depth=clamp(Number(this.moveSelection.depth)||1,1,this.model.size),width=clamp(Number(this.moveSelection.width)||1,1,this.model.size-depth+1);
    this.onMove({face:d.hit.face,depth,width,turns:(Math.abs(cross)>10?cross:dx+dy)>=0?1:-1});
  }
  cancelDrag(){
    const id=this.drag?.pointerId;this.drag=null;this.canvas.classList.remove('dragging');
    if(id!==undefined&&this.canvas.hasPointerCapture?.(id))this.canvas.releasePointerCapture(id);
  }
  destroy(){
    this.disposed=true;this.cancelTurn();this.cancelDrag();this.resize.disconnect();
    for(const [type,handler,options] of this.listeners)this.canvas.removeEventListener(type,handler,options);
  }
}
