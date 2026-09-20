// Animate joints, never the whole building or its construction meshes.
export function jointMotion(atlas,object,{mode='sway',property='rotation',axis='z',speed=1,amplitude=.1,phase=0,curve}={}){
 const track={object,mode,property,axis,speed,amplitude,phase,curve,base:object[property][axis],origin:object.position.clone()};
 atlas.detailMotion??=[];atlas.detailMotion.push(track);return object;
}
export function updateArchitecturalMotion(tracks,time,reduced=false){
 for(const m of tracks||[]){
  const {object,axis,speed}=m;
  if(m.mode==='path'){if(reduced)object.position.copy(m.origin);else m.curve.getPoint((time*speed+m.phase)%1,object.position);continue;}
  const property=m.property||'rotation',base=m.base||0;
  const delta=reduced?0:m.mode==='sway'?Math.sin(time*speed+m.phase)*m.amplitude:m.mode==='lift'?(1-Math.cos(time*speed+m.phase))*m.amplitude/2:time*speed;
  object[property][axis]=base+delta;
 }
}
