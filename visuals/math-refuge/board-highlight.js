// Temporary spoken references are separate from permanent chalk annotations.
// Targets are semantic source rows; the renderer measures their actual glyphs.
const clamp=x=>Math.max(0,Math.min(1,x));
const smooth=x=>{x=clamp(x);return x*x*(3-2*x);};
export const HIGHLIGHT_SECONDS=3.6;
const references=[
 {phrase:'固定右边',tex:'M(u)=',side:'right',operator:'=',relation:1},
 {phrase:'右侧权指数为零',tex:'C_{d,k,\\ell,\\gamma}\\int',side:'right',operator:'≥'},
 {phrase:'右侧权也少一次',tex:'C_{d,k,\\ell,\\gamma}\\int',side:'right',operator:'≥'},
 {phrase:'Laplace 的右边',tex:'\\Delta\\rho=1-\\rho',side:'right',operator:'='},
 {phrase:'得到这一式',tex:'\\mathbb E_\\mu(W_0f^2)\\leq',side:'whole'},
 {phrase:'第一项是函数平方的熵',tex:'\\mathbb E_\\mu(W_0f^2)\\leq',side:'right',operator:'≤',term:0},
 {phrase:'第二项是坏势的指数矩',tex:'\\mathbb E_\\mu(W_0f^2)\\leq',side:'right',operator:'≤',term:1},
 {phrase:'左侧则是',tex:'\\mathbb E_\\mu(W_0f^2)\\leq',side:'left',operator:'≤'},
 {phrase:'右侧正好合成',tex:'\\operatorname{Ent}_\\mu(f^2)\\leq',side:'right',operator:'≤'},
 {phrase:'所得不等式左边',tex:'[1-\\alpha(1+o_d(1))]',side:'left',operator:'≥'},
 {phrase:'右边是负阿尔法',tex:'[1-\\alpha(1+o_d(1))]',side:'right',operator:'≥'},
 {phrase:'再除掉左边的系数',tex:'[1-\\alpha(1+o_d(1))]',side:'left',operator:'≥'},
 {phrase:'可移到左侧的能量项',tex:'[1-\\alpha(1+o_d(1))]',side:'left',operator:'≥'},
 // Keep the correction coefficient separate from the gradient norm.
 {phrase:'除以左边修正系数',tex:'\\frac{-G(\\alpha)}',side:'right',operator:'≥',until:'∫'}
];
export function narrationHighlights(manifest){
 if(!manifest?.paragraphs)return [];
 const result=[];
 for(const p of manifest.paragraphs){
  const b=manifest.boards.find(b=>b.page===p.page);if(!b?.lineCues?.length)continue;
  for(const spec of references){
   const position=p.text.indexOf(spec.phrase);if(position<0)continue;
   const cue=b.lineCues.find(c=>c.source?.tex?.includes(spec.tex));if(!cue)continue;
   const mark=p.referenceTimes?.[spec.phrase];
   const time=Number.isFinite(mark)?p.start+mark:p.start+(p.end-p.start)*position/Math.max(1,p.text.length);
   result.push({...spec,id:p.page+':'+p.paragraph+':'+spec.phrase,page:p.page,row:cue.row,time,writeStart:cue.writeStart,writeEnd:cue.writeEnd,pageEnd:b.end,timing:Number.isFinite(mark)?'aligned':'estimated'});
  }
 }
 return result.sort((a,b)=>a.time-b.time);
}
function union(rects){if(!rects.length)return null;const x=Math.min(...rects.map(r=>r[0])),y=Math.min(...rects.map(r=>r[1])),right=Math.max(...rects.map(r=>r[0]+r[2])),bottom=Math.max(...rects.map(r=>r[1]+r[3]));return [x,y,right-x,bottom-y];}
function symbols(rows,symbol){const seen=new Set();return rows.filter(r=>r.topLevel&&r.symbol===symbol&&r.symbolRect).map(r=>r.symbolRect).filter(r=>{const key=r.map(v=>v.toFixed(2)).join(':');if(seen.has(key))return false;seen.add(key);return true;}).sort((a,b)=>a[0]-b[0]);}
export function measuredHighlight(spec,rows,plan){
 if(!rows||!plan?.segments?.length)return null;
 let indexes=rows.map((r,i)=>r.mainLine===spec.row?i:-1).filter(i=>i>=0);if(!indexes.length)return null;
 const line=union(indexes.map(i=>rows[i]));let left=line[0],right=line[0]+line[2];
 if(spec.side!=='whole'){
  const operators=symbols(indexes.map(i=>rows[i]),spec.operator),divider=operators[spec.relation||0];
  // A missing operator must never fall back to the geometric midpoint.
  if(!divider)return null;
  if(spec.side==='left')right=divider[0]-2;else left=divider[0]+divider[2]+2;
  if(spec.term!==undefined){const plus=symbols(indexes.map(i=>rows[i]),'+').find(r=>r[0]>left);if(!plus)return null;if(spec.term===0)right=plus[0]-2;else left=plus[0]+plus[2]+2;}
  if(spec.until){const boundary=symbols(indexes.map(i=>rows[i]),spec.until).find(r=>r[0]>left);if(!boundary)return null;right=boundary[0]-2;}
  indexes=indexes.filter(i=>rows[i][0]+rows[i][2]/2>=left&&rows[i][0]+rows[i][2]/2<=right);
 }
 if(!indexes.length)return null;
 const ink=union(indexes.map(i=>rows[i]));
 const range=plan.segments.filter(s=>s.mainLine===spec.row),selected=new Set(indexes);
 const start=range[0]?.start,end=range.at(-1)?.end,needed=Math.max(...range.filter(s=>selected.has(s.row)).map(s=>s.end));
 if(!Number.isFinite(needed)||end<=start)return null;
 const visibleAt=spec.writeStart+(spec.writeEnd-spec.writeStart)*clamp((needed-start)/(end-start));
 const begin=Math.max(spec.time,visibleAt+.06),duration=Math.min(HIGHLIGHT_SECONDS,spec.pageEnd-begin-.1);
 if(duration<.8)return null;
 return {...spec,begin,duration,visibleAt,rect:ink};
}
export function highlightFrame(cues,time,{page,enabled=true,visible=true}={}){
 if(!enabled||!visible)return null;
 const c=cues.findLast(c=>c.page===page&&time>=c.begin&&time<c.begin+c.duration);if(!c)return null;
 const age=time-c.begin,fade=Math.min(.8,c.duration*.3),alpha=smooth(age/.22)*(1-smooth((age-(c.duration-fade))/fade));
 return {...c,age,alpha,reveal:smooth(age/.55)};
}
export function laserLifetimeAlpha(elapsed,duration=HIGHLIGHT_SECONDS){return 1-smooth((elapsed-(duration-.8))/.8);}
export function laserPoints(rect,seed=0,count=96){
 const [x,y,w,h]=rect,cx=x+w/2,cy=y+h/2,rx=w/2+14,ry=h/2+12,phase=(seed%37)*.31;
 return Array.from({length:count+1},(_,i)=>{const a=-Math.PI*.68+i/count*Math.PI*2,warp=1+.032*Math.sin(3*a+phase)+.018*Math.sin(5*a+phase*.7),px=rx*Math.cos(a)*warp,py=ry*Math.sin(a)*(1+.045*Math.sin(2*a+phase));return [cx+px-.018*py,cy+py+.018*px];});
}
export function createBoardHighlight(THREE,{width,height,pixels=[1536,640]}={}){
 const rings=Array.from({length:2},()=>{
  const material=new THREE.ShaderMaterial({transparent:true,depthWrite:false,depthTest:true,toneMapped:false,uniforms:{opacity:{value:0},reveal:{value:0}},vertexShader:'attribute float arc;attribute float side;varying float vArc;varying float vSide;void main(){vArc=arc;vSide=side;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.0);}',fragmentShader:'uniform float opacity;uniform float reveal;varying float vArc;varying float vSide;void main(){float head=1.0-smoothstep(reveal-.018,reveal,vArc);float glow=.16*exp(-vSide*vSide*3.0)+.8*exp(-vSide*vSide*30.0);gl_FragColor=vec4(1.0,.24,.12,opacity*head*glow);}'});
  const mesh=new THREE.Mesh(new THREE.BufferGeometry(),material);mesh.name='Temporary spoken laser reference';mesh.visible=false;mesh.renderOrder=5;mesh.matrixAutoUpdate=false;mesh.updateMatrix();return {mesh,id:null,alpha:0};
 });let current=null,cursor=0;
 function shape(ring,frame,parent){
  const points=laserPoints(frame.rect,frame.page*13+frame.row),position=[],arc=[],side=[];
  const mapped=points.map(([x,y])=>[(x/pixels[0]-.5)*width,(.5-y/pixels[1])*height]);
  const half=.024,edge=(i,s)=>{const a=mapped[Math.max(0,i-1)],b=mapped[Math.min(mapped.length-1,i+1)],dx=b[0]-a[0],dy=b[1]-a[1],d=Math.hypot(dx,dy)||1;return [mapped[i][0]-dy/d*half*s,mapped[i][1]+dx/d*half*s,.026];};
  for(let i=0;i<points.length-1;i++)for(const [k,s] of [[i,-1],[i+1,-1],[i,1],[i,1],[i+1,-1],[i+1,1]]){position.push(...edge(k,s));arc.push(k/(points.length-1));side.push(s);}
  const geometry=new THREE.BufferGeometry();geometry.setAttribute('position',new THREE.Float32BufferAttribute(position,3));geometry.setAttribute('arc',new THREE.Float32BufferAttribute(arc,1));geometry.setAttribute('side',new THREE.Float32BufferAttribute(side,1));ring.mesh.geometry.dispose();ring.mesh.geometry=geometry;parent.add(ring.mesh);ring.id=frame.id;ring.alpha=0;ring.elapsed=frame.age;ring.lastAge=frame.age;ring.mesh.userData.reference={page:frame.page,row:frame.row,side:frame.side};
 }
 return {
  update(frame,parent,dt,reduced=false){
   if(frame&&parent){if(!current||current.id!==frame.id||current.mesh.parent!==parent){current=rings[cursor++%2];shape(current,frame,parent);}if(frame.age<current.lastAge-.25)current.elapsed=frame.age;else current.elapsed=Math.max(current.elapsed+Math.max(0,dt),frame.age);current.lastAge=frame.age;current.mesh.material.uniforms.reveal.value=reduced?1:smooth(current.elapsed/.55);}
   else current=null;
   for(const ring of rings){const target=ring===current?smooth(ring.elapsed/.22)*laserLifetimeAlpha(ring.elapsed,frame.duration):0;ring.alpha=reduced?target:ring.alpha+(target-ring.alpha)*(1-Math.exp(-18*Math.max(0,dt)));ring.mesh.visible=ring.alpha>.002;ring.mesh.material.uniforms.opacity.value=ring.alpha;}
   return current&&current.alpha>.002?{...frame,alpha:current.alpha}:null;
  },
  hide(){current=null;for(const ring of rings){ring.alpha=0;ring.mesh.visible=false;ring.mesh.material.uniforms.opacity.value=0;}},
  dispose(){for(const ring of rings){ring.mesh.removeFromParent();ring.mesh.geometry.dispose();ring.mesh.material.dispose();}}
 };
}
