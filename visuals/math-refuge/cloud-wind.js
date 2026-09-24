// Meteorological FROM bearing; scene +X = east and +Z = south. Output km/s.
export function windVelocity(speed,bearing){
 const a=(Number.isFinite(bearing)?bearing:225)*Math.PI/180,s=Math.max(0,Number(speed)||0)/3600;
 return {x:-Math.sin(a)*s,z:Math.cos(a)*s};
}
export function advanceCloudWind(state,speed,bearing,dt){
 const target=windVelocity(speed,bearing),t=Math.max(0,Math.min(3,dt)),e=Math.exp(-t/4);
 for(const axis of ['x','z']){const old=state.velocity[axis];state.offset[axis]+=target[axis]*t+(old-target[axis])*4*(1-e);state.velocity[axis]=target[axis]+(old-target[axis])*e;}
 return state;
}
