import {FACELETS, FACES, NORMALS, BASIS, MOVE_INFO, identity, inverse, compose, movePermutation} from './cube-core.mjs';
const PALETTE={U:'#eee5cd',R:'#b96854',F:'#759d8b',D:'#d8b775',L:'#d09263',B:'#668da9'};
const add=(a,b)=>a.map((v,i)=>v+b[i]);
const scale=(a,s)=>a.map(v=>v*s);
export function rotate(v,axis,a){const c=Math.cos(a),s=Math.sin(a),[x,y,z]=v;return axis===0?[x,c*y-s*z,s*y+c*z]:axis===1?[c*x+s*z,y,-s*x+c*z]:[c*x-s*y,s*x+c*y,z];}
const ease=t=>t<.5?4*t*t*t:1-Math.pow(-2*t+2,3)/2;
function polygon(ctx,points,r=0){points=points.map(p=>p.slice(0,2));ctx.beginPath();if(!r){points.forEach(([x,y],i)=>i?ctx.lineTo(x,y):ctx.moveTo(x,y));}else{points.forEach((p,i)=>{const prev=points[(i+points.length-1)%points.length],next=points[(i+1)%points.length],a=p.map((v,j)=>v*(1-r)+prev[j]*r),b=p.map((v,j)=>v*(1-r)+next[j]*r);if(i===0)ctx.moveTo(...a);else ctx.lineTo(...a);ctx.quadraticCurveTo(...p,...b);});}ctx.closePath();}
function contains(p,vs){let inside=false;for(let i=0,j=vs.length-1;i<vs.length;j=i++){const a=vs[i],b=vs[j];if((a[1]>p[1])!==(b[1]>p[1])&&p[0]<(b[0]-a[0])*(p[1]-a[1])/(b[1]-a[1])+a[0])inside=!inside;}return inside;}
export class CubeView {
  constructor(canvas,{onMove=()=>{},onInspect=()=>{}}={}){
    this.canvas=canvas;this.ctx=canvas.getContext('2d');this.state=identity();this.yaw=-.64;this.pitch=.46;this.labels=false;this.highlight=false;this.duration=350;this.onMove=onMove;this.onInspect=onInspect;this.hit=[];this.version=0;
    this.resize=new ResizeObserver(()=>this.draw());this.resize.observe(canvas);
    canvas.addEventListener('contextmenu',e=>e.preventDefault());
    canvas.addEventListener('pointerdown',e=>this.pointerDown(e));
    canvas.addEventListener('pointermove',e=>this.pointerMove(e));
    canvas.addEventListener('pointerup',e=>this.pointerUp(e));
    canvas.addEventListener('pointercancel',()=>{this.drag=null;canvas.classList.remove('dragging');});
    this.draw();
  }
  setState(p){this.version++;if(this.resolve){this.resolve(false);this.resolve=null;}this.animation=null;this.state=[...p];this.draw();}
  home(){this.yaw=-.64;this.pitch=.46;this.draw();}
  project(p){const v=rotate(rotate(p,1,this.yaw),0,this.pitch),k=11/(11-v[2]);return [this.w/2+v[0]*this.unit*k,this.h/2-v[1]*this.unit*k,v[2]];}
  viewNormal(n){return rotate(rotate(n,1,this.yaw),0,this.pitch);}
  transform(p,location){return this.animation&&location[this.animation.axis]===this.animation.layer?rotate(p,this.animation.axis,this.animation.angle):p;}
  normal(n,location){return this.animation&&location[this.animation.axis]===this.animation.layer?rotate(n,this.animation.axis,this.animation.angle):n;}
  draw(){
    const rect=this.canvas.getBoundingClientRect();if(!rect.width||!rect.height)return;
    const dpr=Math.min(devicePixelRatio||1,2);this.w=rect.width;this.h=rect.height;this.unit=Math.min(this.w/5.55,this.h/5.65);
    if(this.canvas.width!==Math.round(this.w*dpr)||this.canvas.height!==Math.round(this.h*dpr)){this.canvas.width=Math.round(this.w*dpr);this.canvas.height=Math.round(this.h*dpr);}
    const ctx=this.ctx;ctx.setTransform(dpr,0,0,dpr,0,0);ctx.clearRect(0,0,this.w,this.h);
    const shadow=ctx.createRadialGradient(this.w/2,this.h*.87,2,this.w/2,this.h*.87,this.unit*1.8);shadow.addColorStop(0,'rgba(0,0,0,.36)');shadow.addColorStop(1,'rgba(0,0,0,0)');ctx.fillStyle=shadow;ctx.save();ctx.translate(0,this.h*.65);ctx.scale(1,.25);ctx.fillRect(0,0,this.w,this.h);ctx.restore();
    const faces=[], at=inverse(this.state);
    for(let x=-1;x<=1;x++)for(let y=-1;y<=1;y++)for(let z=-1;z<=1;z++){
      if(!x&&!y&&!z)continue;const loc=[x,y,z],center=scale(loc,1.025);
      for(const f of FACES){const n=NORMALS[f],normal=this.normal(n,loc);if(this.viewNormal(normal)[2]<=.015)continue;const [r,u]=BASIS[f];
        const centerFace=add(center,scale(n,.493));
        const pts=[[-1,1],[1,1],[1,-1],[-1,-1]].map(([a,b])=>this.project(this.transform(add(centerFace,add(scale(r,a*.493),scale(u,b*.493))),loc)));
        faces.push({pts,z:pts.reduce((s,p)=>s+p[2],0)/4,body:true,light:this.viewNormal(normal)[2]});
      }
    }
    FACELETS.forEach((s,i)=>{
      const normal=this.normal(s.n,s.p);if(this.viewNormal(normal)[2]<=.015)return;
      const center=add(scale(s.p,1.025),scale(s.n,.498)),[r,u]=BASIS[s.face];
      const pts=[[-1,1],[1,1],[1,-1],[-1,-1]].map(([a,b])=>this.project(this.transform(add(center,add(scale(r,a*.419),scale(u,b*.419))),s.p)));
      faces.push({pts,z:pts.reduce((a,p)=>a+p[2],0)/4,body:false,face:s.face,id:i,color:FACELETS[at[i]].face,label:s.row===1&&s.col===1?s.face:FACELETS[at[i]].label,moved:at[i]!==i,light:this.viewNormal(normal)[2],center:this.project(this.transform(center,s.p))});
    });
    faces.sort((a,b)=>a.z-b.z);this.hit=[];
    for(const f of faces){polygon(ctx,f.pts,f.body?.10:.13);
      if(f.body){ctx.fillStyle=`rgb(${24+f.light*9},${23+f.light*8},${20+f.light*7})`;ctx.fill();ctx.strokeStyle='rgba(220,197,142,.065)';ctx.lineWidth=.7;ctx.stroke();continue;}
      ctx.fillStyle=PALETTE[f.color];ctx.fill();
      ctx.save();ctx.clip();const g=ctx.createLinearGradient(f.pts[0][0],f.pts[0][1],f.pts[2][0],f.pts[2][1]);g.addColorStop(0,'rgba(255,246,215,.15)');g.addColorStop(.45,'rgba(255,255,255,0)');g.addColorStop(1,`rgba(0,0,0,${.17+(1-f.light)*.12})`);ctx.fillStyle=g;ctx.fill();ctx.restore();
      ctx.strokeStyle=this.highlight&&f.moved?'#fff0b7':'rgba(255,239,197,.2)';ctx.lineWidth=this.highlight&&f.moved?2:.8;ctx.stroke();
      if(this.highlight&&!f.moved){ctx.fillStyle='rgba(12,13,12,.53)';ctx.fill();}
      if(this.labels||f.id%9===4){ctx.font=`${f.id%9===4?'500':'400'} ${Math.max(9,this.unit*(f.id%9===4?.19:.14))}px Inter, sans-serif`;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillStyle='rgba(18,22,20,.78)';ctx.fillText(this.labels?f.label:f.face,f.center[0],f.center[1]);}
      this.hit.push(f);
    }
  }
  turn(move){
    if(this.animation)return Promise.resolve(false);const version=++this.version,{axis,layer,angle}=MOVE_INFO[move.face],duration=this.duration*(move.turns===2?1.3:1),start=performance.now();
    return new Promise(resolve=>{this.resolve=resolve;const frame=now=>{
      if(this.version!==version)return;const t=duration?Math.min(1,(now-start)/duration):1;this.animation={axis,layer,angle:angle*move.turns*ease(t)};this.draw();
      if(t<1)requestAnimationFrame(frame);else{this.state=compose(this.state,movePermutation(move));this.animation=null;this.resolve=null;this.draw();resolve(true);}
    };requestAnimationFrame(frame);});
  }
  point(e){const r=this.canvas.getBoundingClientRect();return [e.clientX-r.left,e.clientY-r.top];}
  pointerDown(e){if(e.button!==0&&e.button!==2)return;const p=this.point(e),hit=[...this.hit].reverse().find(f=>contains(p,f.pts));this.drag={p,last:p,hit:e.button===2||e.shiftKey?null:hit,moved:false};this.canvas.setPointerCapture(e.pointerId);this.canvas.classList.add('dragging');this.canvas.focus({preventScroll:true});}
  pointerMove(e){if(!this.drag)return;const p=this.point(e),d=this.drag,dx=p[0]-d.last[0],dy=p[1]-d.last[1];if(Math.hypot(p[0]-d.p[0],p[1]-d.p[1])>8)d.moved=true;if(!d.hit){this.yaw+=dx*.009;this.pitch=Math.max(-1.35,Math.min(1.35,this.pitch+dy*.009));this.draw();}d.last=p;}
  pointerUp(e){const d=this.drag;this.drag=null;this.canvas.classList.remove('dragging');if(!d||!d.hit)return;const p=this.point(e),dx=p[0]-d.p[0],dy=p[1]-d.p[1];if(!d.moved){this.onInspect(d.hit);return;}const c=this.project(scale(NORMALS[d.hit.face],1.523)),rx=d.p[0]-c[0],ry=d.p[1]-c[1],cross=rx*dy-ry*dx;this.onMove({face:d.hit.face,turns:(Math.abs(cross)>10?cross:dx+dy)>=0?1:-1});}
}
