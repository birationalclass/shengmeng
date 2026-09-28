// One slow, closed arc. Zero velocity at the initial viewpoint and at each turn.
export function hallOrbit(eye,target,seconds){
 const u=(1-Math.cos(2*Math.PI*seconds/100))*.5,angle=.20*u;
 const dx=eye[0]-target[0],dz=eye[2]-target[2],scale=1-.025*u;
 return [target[0]+(dx*Math.cos(angle)-dz*Math.sin(angle))*scale,eye[1]+.25*u,target[2]+(dx*Math.sin(angle)+dz*Math.cos(angle))*scale];
}
