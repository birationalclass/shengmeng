import * as T from '../vendor/three.module.js';
import {profile,sampleSection} from './stroke-volume.js';
import {sampleRailSection} from './yang-volume.js';
import {prepareVolume} from './surface.js';
import {guardRailBends} from './bend-guard.js';
import {attachStrokeLink} from './stroke-link.js';
import {combineContinuousRuns} from './continuous-run.js';
import {makePenTransfer} from './pen-transfer.js';

// Our implementation, informed by Floating Strokes, §4.1–4.2.
// Authored planar gestures remain the source. The overlap raster and smooth
// contact relaxation below are our own discretization, not the authors' code.
const clamp=T.MathUtils.clamp,KEYS=49;
const lerpField=(field,u)=>{const x=clamp(u,0,1)*(field.length-1),i=Math.min(field.length-2,Math.floor(x));return T.MathUtils.lerp(field[i],field[i+1],x-i);};
function parameterAtArc(spec,u){let lo=0,hi=spec.count;const target=u*spec.length;while(hi-lo>1){const m=(lo+hi)>>1;if(spec.sections[m].length<target)lo=m;else hi=m;}return (lo+(target-spec.sections[lo].length)/Math.max(1e-12,spec.sections[hi].length-spec.sections[lo].length))/spec.count;}
function refresh(spec){
 let length=0;
 spec.sections.forEach((q,i)=>{
  const before=spec.sections[Math.max(0,i-2)].center,after=spec.sections[Math.min(spec.count,i+2)].center;
  q.tangent.copy(after).sub(before).normalize();
  const d=q.b.clone().sub(q.a);if(!spec.boundaryLoft)d.addScaledVector(q.tangent,-d.dot(q.tangent));
  q.a.copy(q.center).addScaledVector(d,-.5);q.b.copy(q.center).addScaledVector(d,.5);
  const n=new T.Vector3().crossVectors(q.tangent,d).normalize();if(n.lengthSq()>.1)q.normal.copy(n);
  if(i)length+=q.center.distanceTo(spec.sections[i-1].center);q.length=length;
 });spec.length=length;
 return spec;
}
function asRail(spec,kind){
 if(kind==='rail')return spec;
 const sections=[],count=600,front=[],back=[];
 for(let i=0;i<=count;i++){
  const q=sampleSection(spec,i/count);
  sections.push({a:q.center.clone().addScaledVector(q.n,-q.width),b:q.center.clone().addScaledVector(q.n,q.width),center:q.center,normal:q.b,tangent:q.tan,length:0});
 }
 for(let i=0;i<KEYS;i++){
  const q=sampleSection(spec,clamp(i/(KEYS-1),.0001,.9999)),v=q.thickness/Math.max(1e-8,2*q.width);front.push(v);back.push(v);
 }
 return refresh({...spec,sections,count,front,back,crown:[.5,.5],rearCrown:[.5,.5],camber:[0,0],capStart:0,capEnd:0});
}
function peakThickness(spec){let peak=0;for(let i=1;i<32;i++){const q=sampleRailSection(spec,i/32);peak=Math.max(peak,q.front+q.back);}return peak;}
function refineStroke(spec,settings,mean){
 if(spec.brush){const amount=(settings.harmony-.5)*clamp(mean/Math.max(1e-8,peakThickness(spec))-1,-.25,.25);spec.front=spec.front.map(v=>v*(1+amount));spec.back=spec.back.map(v=>v*(1+amount));spec.spatial=true;return spec;}
 const count=spec.count,turns=[],pressure=[],oldFront=spec.front,oldBack=spec.back,oldCrown=spec.crown||[.5,.5],oldCamber=spec.camber||[0,0];
 let lastHeading=Math.atan2(spec.sections[0].tangent.y,spec.sections[0].tangent.x),accumulated=0,maxWidth=0;
 spec.sections.forEach((q,i)=>{
  const angle=Math.atan2(q.tangent.y,q.tangent.x);let delta=angle-lastHeading;while(delta>Math.PI)delta-=Math.PI*2;while(delta<-Math.PI)delta+=Math.PI*2;
  accumulated+=delta;lastHeading=angle;turns.push(accumulated);maxWidth=Math.max(maxWidth,q.a.distanceTo(q.b));
 });
 const peak=peakThickness(spec),harmonize=1+settings.harmony*clamp(mean/Math.max(peak,1e-7)-1,-.24,.20);
 const front=[],back=[],crown=[],camber=[];
 for(let i=0;i<KEYS;i++){
  const u=i/(KEYS-1),q=sampleRailSection(spec,u),press=q.width/Math.max(1e-6,maxWidth),turn=lerpField(turns,parameterAtArc(spec,u));
  pressure.push(press);
  // A pressed belly is full, but a lifted turn remains narrow. Width and
  // front/back volumes are independent, rather than a constant round tube.
  front.push(profile(oldFront,u)*(.74+.12*press)*harmonize);
  back.push(profile(oldBack,u)*(.67+.07*press)*harmonize);
  crown.push(clamp(profile(oldCrown,u)+.045*settings.turn*Math.tanh(turn),.30,.70));
  camber.push(profile(oldCamber,u)+.018*settings.turn*Math.tanh(turn)*Math.sin(Math.PI*u)**2);
 }
 const amplitude=Math.min(.16,spec.length*.065)*settings.turn*settings.depth;
 spec.sections.forEach((q,i)=>{
  const u=q.length/Math.max(1e-12,spec.length),turn=turns[i],window=Math.sin(Math.PI*u)**2;
  const lift=amplitude*Math.tanh(turn*.9)*window;
  const d=q.b.clone().sub(q.a).applyAxisAngle(q.tangent,.19*settings.turn*settings.depth*Math.tanh(turn)*window);
  q.center.z+=lift;q.a.copy(q.center).addScaledVector(d,-.5);q.b.copy(q.center).addScaledVector(d,.5);
 });
 Object.assign(spec,{front,back,crown,camber,safeBend:true,spatial:true,surfaceStyle:'lens',sectionPower:[2.25,2.7,2.4]});refresh(spec);guardRailBends(spec);refresh(spec);
 return spec;
}
function cross(a,b,p){return (b.x-a.x)*(p.y-a.y)-(b.y-a.y)*(p.x-a.x);}
function triangle(p,a,b,c){const x=cross(a,b,p),y=cross(b,c,p),z=cross(c,a,p);return (x>=-1e-9&&y>=-1e-9&&z>=-1e-9)||(x<=1e-9&&y<=1e-9&&z<=1e-9);}
function rasterize(spec,grid){
 const cells=new Map(),steps=96,rows=grid.resolution,sections=Array.from({length:steps+1},(_,i)=>sampleRailSection(spec,i/steps));
 for(let j=0;j<steps;j++){
  const q=sections[j],r=sections[j+1],poly=[q.a,q.b,r.b,r.a],xs=poly.map(p=>p.x),ys=poly.map(p=>p.y);
  const loX=clamp(Math.floor((Math.min(...xs)-grid.x)/grid.step),0,rows-1),hiX=clamp(Math.floor((Math.max(...xs)-grid.x)/grid.step),0,rows-1),loY=clamp(Math.floor((Math.min(...ys)-grid.y)/grid.step),0,rows-1),hiY=clamp(Math.floor((Math.max(...ys)-grid.y)/grid.step),0,rows-1);
  for(let y=loY;y<=hiY;y++)for(let x=loX;x<=hiX;x++){
   const p={x:grid.x+(x+.5)*grid.step,y:grid.y+(y+.5)*grid.step};
   if(!triangle(p,...poly.slice(0,3))&&!triangle(p,poly[0],poly[2],poly[3]))continue;
   const d=r.center.clone().sub(q.center),l=d.x*d.x+d.y*d.y,t=clamp(((p.x-q.center.x)*d.x+(p.y-q.center.y)*d.y)/Math.max(1e-12,l),0,1),u=(j+t)/steps;
   const distance=(p.x-q.center.x-d.x*t)**2+(p.y-q.center.y-d.y*t)**2,id=y*rows+x;
   if(!cells.has(id)||distance<cells.get(id).distance)cells.set(id,{u,p,distance});
  }
 }return cells;
}
function height(spec,cell){
 const q=sampleRailSection(spec,cell.u),d=q.b.clone().sub(q.a),t=clamp(((cell.p.x-q.a.x)*d.x+(cell.p.y-q.a.y)*d.y)/Math.max(1e-9,d.x*d.x+d.y*d.y),0,1);
 const arch=Math.sqrt(Math.max(0,4*t*(1-t))),z=T.MathUtils.lerp(q.a.z,q.b.z,t)+q.n.z*q.camber*arch*arch;
 const f=q.n.z*q.front*arch,b=-q.n.z*q.back*arch;
 return {lo:z+Math.min(f,b),hi:z+Math.max(f,b),z,width:q.width};
}
function contacts(parts,settings){
 const constraints=[],groups=new Map();let overlaps=0,regions=0;
 parts.forEach((part,i)=>{const id=part.stroke.character||0;if(!groups.has(id))groups.set(id,[]);groups.get(id).push(i);});
 for(const ids of groups.values()){
  const box=new T.Box3();ids.forEach(i=>parts[i].spec.sections.forEach(q=>{box.expandByPoint(q.a);box.expandByPoint(q.b);}));
  const size=box.getSize(new T.Vector3()),span=Math.max(size.x,size.y),step=(span+.08)/128,grid={x:box.min.x-.04,y:box.min.y-.04,step,resolution:128};
  const rasters=ids.map(i=>rasterize(parts[i].spec,grid));
  for(let j=1;j<ids.length;j++)for(let k=0;k<j;k++){
   const a=rasters[k],b=rasters[j],common=new Set([...b.keys()].filter(id=>a.has(id)));
   const firstStroke=parts[ids[k]].stroke,laterStroke=parts[ids[j]].stroke,
    laterOver=laterStroke.over?.includes(firstStroke.role),firstOver=firstStroke.over?.includes(laterStroke.role),authoredOrder=Boolean(laterOver||firstOver);
   if(common.size<3||(!authoredOrder&&common.size/Math.max(1,Math.min(a.size,b.size))<.045))continue;overlaps++;
   while(common.size){
    const seed=common.values().next().value,queue=[seed],region=[];common.delete(seed);
    for(let at=0;at<queue.length;at++){
     const id=queue[at];region.push(id);const x=id%128,y=Math.floor(id/128);
     for(let yy=Math.max(0,y-1);yy<=Math.min(127,y+1);yy++)for(let xx=Math.max(0,x-1);xx<=Math.min(127,x+1);xx++){const next=yy*128+xx;if(common.delete(next))queue.push(next);}
    }
    if(region.length<3)continue;regions++;
    const samples=region.map(id=>({a:a.get(id),b:b.get(id)}));
    const center=samples[Math.floor(samples.length/2)],ha=height(parts[ids[k]].spec,center.a),hb=height(parts[ids[j]].spec,center.b);
    // Preserve a clearly authored underpass. Nearly coplanar crossings follow
    // writing order; do not flatten an existing deliberate interweave.
    const backwards=authoredOrder?Boolean(firstOver):hb.z<ha.z-(ha.hi-ha.lo+hb.hi-hb.lo)*.60;
    samples.sort((x,y)=>x.b.u-y.b.u);
    for(let v=0;v<Math.min(7,samples.length);v++){
     const sample=samples[Math.floor(v*(samples.length-1)/Math.max(1,Math.min(7,samples.length)-1))],first=height(parts[ids[k]].spec,sample.a),later=height(parts[ids[j]].spec,sample.b),gap=span*(authoredOrder?.022:.009*settings.layering);
     const upper=backwards?ids[k]:ids[j],lower=backwards?ids[j]:ids[k],up=backwards?sample.a:sample.b,low=backwards?sample.b:sample.a;
     const required=backwards?later.hi-first.lo+gap:first.hi-later.lo+gap;
     const sigma=clamp((first.width+later.width)/Math.max(parts[upper].spec.length,1e-5)*.85,.075,.24);
     constraints.push({upper,lower,u:up.u,v:low.u,point:[up.p.x,up.p.y],required:required*(authoredOrder?Math.min(1,settings.depth):settings.layering*settings.depth),sigma,limit:span*(authoredOrder?.40:.21),authoredOrder});
    }
   }
  }
 }return {constraints,overlaps,regions};
}
function relax(parts,constraints){
 const fields=parts.map(()=>Array(KEYS).fill(0));
 for(let pass=0;pass<48;pass++){
  for(const c of constraints){
   const error=c.required-(lerpField(fields[c.upper],c.u)-lerpField(fields[c.lower],c.v));if(error<=.0001)continue;
   for(let i=0;i<KEYS;i++){
    const u=i/(KEYS-1),a=Math.exp(-.5*((u-c.u)/c.sigma)**2),b=Math.exp(-.5*((u-c.v)/c.sigma)**2);
    fields[c.upper][i]=clamp(fields[c.upper][i]+error*.43*a,-c.limit,c.limit);fields[c.lower][i]=clamp(fields[c.lower][i]-error*.19*b,-c.limit,c.limit);
   }
  }
  // Bending regularization avoids tiny local humps and alternating Z ripples.
  for(const field of fields){const prev=field.slice();for(let i=1;i<KEYS-1;i++)field[i]=prev[i]*.84+(prev[i-1]+prev[i+1])*.08;}
 }
 let maxLift=0;
 parts.forEach((part,index)=>{
  const spec=part.spec;
  spec.sections.forEach(q=>{const dz=profile(fields[index],q.length/Math.max(1e-12,spec.length));q.a.z+=dz;q.b.z+=dz;q.center.z+=dz;maxLift=Math.max(maxLift,Math.abs(dz));});
  spec.layerOffsets=fields[index];refresh(spec);guardRailBends(spec);refresh(spec);
 });
 const maxResidual=constraints.reduce((max,c)=>Math.max(max,c.required-(lerpField(fields[c.upper],c.u)-lerpField(fields[c.lower],c.v))),0);
 return {maxLift,maxResidual};
}
function pressureMotion(spec,original){
 const times=[0];let total=0;
 for(let i=1;i<=64;i++){
  const u=i/64,q=sampleRailSection(spec,u),before=sampleRailSection(spec,(i-1)/64),heading=q.center.clone().sub(before.center);
  const turn=i>1?heading.angleTo(before.center.clone().sub(sampleRailSection(spec,(i-2)/64).center)):0;
  total+=.5+Math.sqrt(Math.max(0,q.width))*.8+Math.min(1,turn)*1.1;times.push(total);
 }
 const motion=[0];let at=1;
 for(let i=1;i<12;i++){
  const target=i/12*total;while(at<64&&times[at]<target)at++;
  const u=(at-1+(target-times[at-1])/Math.max(1e-9,times[at]-times[at-1]))/64;
  motion.push(.62*profile(original||[0,1],i/12)+.38*u);
 }motion.push(1);return motion;
}
export function prepareSpatialModel(glyph,settings={}){
 const config={fullness:1,depth:1,model:'spatial',writing:'flow',turn:1,layering:1,harmony:.5,connection:'linked',...settings};
 const source=config.model==='legacy'?(glyph.legacyStrokes||glyph.strokes):config.model==='reference-v8'?(glyph.referenceV8Strokes||glyph.strokes):config.model==='reference-v9'?(glyph.referenceV9Strokes||glyph.strokes):config.model==='reference-v10'?(glyph.referenceV10Strokes||glyph.strokes):glyph.strokes;
 const parts=source.map((stroke,sourceIndex)=>{
  const kind=stroke.kind||glyph.kind;let input=stroke;
  if(config.model!=='legacy'&&stroke.detail?.level==='procedural'&&kind==='rail'){
   const centers=stroke.a.map((p,i)=>new T.Vector3(...p).add(new T.Vector3(...stroke.b[i])).multiplyScalar(.5));
   const box=new T.Box3().setFromPoints(centers),size=box.getSize(new T.Vector3()),chord=centers.at(-1).clone().sub(centers[0]);
   const span=Math.hypot(chord.x,chord.y),length=centers.slice(1).reduce((n,p,i)=>n+p.distanceTo(centers[i]),0);
   if(span>.06&&span<.9&&Math.max(size.x,size.y)/Math.max(.02,Math.min(size.x,size.y))<3.2&&length<1.35*span){
    const nx=-chord.y/span,ny=chord.x/span,r=Math.max(...stroke.a.map((p,i)=>Math.hypot(p[0]-stroke.b[i][0],p[1]-stroke.b[i][1])))*.5;
    const a=[],b=[],press=[.18,.56,.86,1,.91,.61,.08];
    for(let i=0;i<press.length;i++){const u=i/(press.length-1),x=T.MathUtils.lerp(centers[0].x,centers.at(-1).x,u),y=T.MathUtils.lerp(centers[0].y,centers.at(-1).y,u),z=(centers[0].z+centers.at(-1).z)*.5+Math.sin(Math.PI*u)*Math.min(.07,span*.12),bank=-.18+.48*u,w=r*press[i];a.push([x-nx*w*Math.cos(bank),y-ny*w*Math.cos(bank),z-w*Math.sin(bank)]);b.push([x+nx*w*Math.cos(bank),y+ny*w*Math.cos(bank),z+w*Math.sin(bank)]);}
    input={...stroke,a,b,front:[.22,.38,.40,.25],back:[.14,.22,.24,.15],capStart:.06,capEnd:.08,safeBend:false,dotRefined:true};
   }
  }
  if(stroke.brush){input={...stroke,a:stroke.a.map((p,i)=>[p[0],p[1],(p[2]+stroke.b[i][2])*.5+(p[2]-stroke.b[i][2])*.5*config.turn]),b:stroke.b.map((p,i)=>[p[0],p[1],(p[2]+stroke.a[i][2])*.5+(p[2]-stroke.a[i][2])*.5*config.turn])};}
  // A closing dot lifts to its farthest tip. A short return into its own
  // pressed belly would fold the cap into a knuckle (not a brush turn).
  if(config.model!=='legacy'&&kind==='rail'&&!stroke.brush&&!input.dotRefined&&/点/.test(stroke.name)){
   const centers=stroke.a.map((p,i)=>new T.Vector3(...p).add(new T.Vector3(...stroke.b[i])).multiplyScalar(.5));let far=0,tip=0;
   centers.forEach((p,i)=>{const d=p.distanceToSquared(centers[0]);if(d>far){far=d;tip=i;}});
   if(tip>1&&tip<centers.length-1){const a=stroke.a.slice(0,tip+1),b=stroke.b.slice(0,tip+1);a[tip]=centers[tip].toArray();b[tip]=centers[tip].toArray();input={...stroke,a,b};}
  }
  return {stroke,kind,spec:prepareVolume(input,kind,config.fullness,config.depth),sourceIndices:[sourceIndex]};
 });
 if(config.model==='legacy')return {parts,report:{revision:'legacy',overlaps:0,regions:0,maxLift:0,maxResidual:0}};
 parts.forEach(part=>{part.spec=asRail(part.spec,part.kind);part.kind='rail';});
 const groups=new Map();parts.forEach(part=>{const id=part.stroke.character||0;if(!groups.has(id))groups.set(id,[]);groups.get(id).push(peakThickness(part.spec));});
 const means=new Map([...groups].map(([id,values])=>[id,values.reduce((a,b)=>a+b,0)/values.length]));
 parts.forEach(part=>refineStroke(part.spec,config,means.get(part.stroke.character||0)));
 const contact=contacts(parts,config),result=relax(parts,contact.constraints);
 const sectionJoins=[];
 parts.forEach((part,index)=>{
  if(!part.stroke.joinFrom)return;
  const prior=parts.find(p=>p.stroke.role===part.stroke.joinFrom&&(p.stroke.character||0)===(part.stroke.character||0));if(!prior)return;
  const a=sampleRailSection(prior.spec,1),b=sampleRailSection(part.spec,0),delta=a.center.clone().sub(b.center);
  const da=a.a.clone().sub(b.a),db=a.b.clone().sub(b.b);
  part.spec.sections.forEach(q=>{const u=q.length/part.spec.length,w=1-T.MathUtils.smootherstep(u,0,.22);q.a.addScaledVector(da,w);q.b.addScaledVector(db,w);q.center.copy(q.a).add(q.b).multiplyScalar(.5);});refresh(part.spec);
  // The harmony control scales each stroke separately. Constrain the shared
  // section after that operation, including its two volume rails and camber.
  for(const [field,fallback] of [['front',0],['back',0],['crown',.5],['rearCrown',.5],['camber',0]]){
   const source=part.spec[field]||[fallback,fallback],target=profile(prior.spec[field]||[fallback,fallback],1);
   part.spec[field]=Array.from({length:KEYS},(_,i)=>{const u=i/(KEYS-1),w=1-T.MathUtils.smootherstep(u,0,.12);return T.MathUtils.lerp(profile(source,u),target,w);});
  }
  prior.spec.stitchEnd=true;part.spec.stitchStart=true;part.spec.joinStartNormal=a.n.toArray();
  sectionJoins.push({from:parts.indexOf(prior),to:index,translation:delta.toArray(),delay:part.stroke.start-prior.stroke.end,
   scope:'Shared boundary section between separately closed stroke meshes; not a Boolean union.'});
 });
 const strokeLinks=[],transfers=[];
 if(config.connection==='separate')parts.forEach(part=>{if(part.spec.boundaryLoft)part.spec.forceReveal=true;});
 parts.forEach((part,index)=>{
  if(!part.stroke.connection)return;part.spec.joinable=true;
  const prior=parts.find(p=>p.stroke.role===part.stroke.connection.from&&(p.stroke.character||0)===(part.stroke.character||0));
  if(prior&&config.connection!=='separate'){
   if(part.stroke.connection.type==='lifted-return'){
    const transfer=makePenTransfer(prior,part);transfers.push(transfer);
    const {curve,...data}=transfer;strokeLinks.push({stroke:index,...data});
   }else if(part.stroke.connection.type==='gesture'){
    strokeLinks.push({stroke:index,type:'temporal-gesture',from:'wind-main',to:'wind-inner',
     sharedTime:prior.stroke.end,delay:part.stroke.start-prior.stroke.end,geometryBridge:false,
     scope:'Successive writing and a shared boundary-growth rule, not a welded inter-stroke connector.'});
   }else{part.spec=attachStrokeLink(part.spec,prior.spec);strokeLinks.push({stroke:index,...part.spec.link});}
  }
 });
 parts.forEach(part=>{part.spec.motion=pressureMotion(part.spec,part.stroke.motion);});
 const rendered=['spatial','reference-v10'].includes(config.model)&&config.connection==='linked'&&config.writing==='flow'?combineContinuousRuns(parts):parts;
 const mappedJoins=sectionJoins.map(join=>{const merged=rendered.some(part=>part.run&&part.sourceIndices.includes(join.from)&&part.sourceIndices.includes(join.to));return {...join,merged,scope:merged?'Internal junction of one closed loft; no closing cap.':join.scope};});
 return {parts:rendered,transfers,report:{revision:config.model==='reference-v9'?'boundary-volume-v9-20261024':config.model==='reference-v10'?'continuous-growth-v10-20261024':'wind-second-to-third-v11-20261024',model:config.model,method:'returning fan contour for stroke 2 / lifted transfer into stroke 3 / authored depth order / matched contours',authoredSegmentCount:source.length,renderedPieceCount:rendered.length,indexSpace:'source segment indices, zero based',transfers:transfers.map(({curve,...data})=>data),continuousRuns:rendered.filter(part=>part.run).map(part=>part.run),manualLensSegments:parts.filter(part=>part.spec.brush).length,automaticDotRepairs:parts.filter(part=>part.spec.dotRefined).length,strokeLinks,sectionJoins:mappedJoins,depthOrder:contact.constraints.filter(c=>c.authoredOrder).map(c=>({upper:c.upper,lower:c.lower,u:c.u,v:c.v,point:c.point,required:c.required})),overlaps:contact.overlaps,regions:contact.regions,constraints:contact.constraints.length,...result,scope:'Stroke 2 returns around the foot to its waist before the lifted move into stroke 3. The optional trajectory guide is not deposited material. Existing inner-to-insect run remains a separate gesture. Local reconstruction; sampled contact checks are not a global collision certificate.',paper:'https://doi.org/10.1145/3736782'}};
}

export function constructionCurves(spec,kind){
 const curves=Array.from({length:5},()=>[]);
 for(let i=0;i<=120;i++){
  const u=i/120;
  if(kind==='rail'){const q=sampleRailSection(spec,u);[q.a,q.b,q.f,q.k,q.center].forEach((p,j)=>curves[j].push(p));}
  else{const q=sampleSection(spec,u);[q.center.clone().addScaledVector(q.n,-q.width),q.center.clone().addScaledVector(q.n,q.width),q.center.clone().addScaledVector(q.b,q.thickness),q.center.clone().addScaledVector(q.b,-q.thickness),q.center].forEach((p,j)=>curves[j].push(p));}
 }return curves.slice(0,4);
}
