// Uniform building enlargement: footprint area doubles, not quadruples.
// Landscape placements expand with it, but outdoor plant sizes stay in metres.
export const BUILDING_SCALE=Math.SQRT2;
export const GIANT_TREES=[[-22,-26,4.2],[-40,9,3.6],[-5,-37,3.8]];
export const BAMBOO_GROVES=[[-34,-13,7,11],[-17,-35,10,5],[31,-25,9,4]];
export const LAWNS=[{x:6,z:20.8,rx:19,rz:4.4},{x:29,z:18.5,rx:9,rz:4}];
// [x, water elevation, z, half-width], all outside the building footprints.
export const RIVER_NODES=[[-41,25,-55,1.8],[-36,23,-48,2.2],[-33,3,-41,2.6],[-30,.6,-33,2],[-28,-.5,-21,1.4],[-27,-1,-6,1.5],[-25,-1.4,10,1.6],[-18,-1.8,23,2],[-3,-2.1,28,2.1],[15,-2.5,29,1.8],[31,-3,28,1.8],[43,-4.5,31,1.6],[52,-9,34,2.4],[60,-9.04,36,3.4]];
const catmull=(a,b,c,d,t)=>.5*((2*b)+(-a+c)*t+(2*a-5*b+4*c-d)*t*t+(-a+3*b-3*c+d)*t*t*t);
export function riverPoint(t){
  const q=Math.max(0,Math.min(1,t))*(RIVER_NODES.length-1),i=Math.min(RIVER_NODES.length-2,Math.floor(q)),f=q-i;
  const a=RIVER_NODES[Math.max(0,i-1)],b=RIVER_NODES[i],c=RIVER_NODES[i+1],d=RIVER_NODES[Math.min(RIVER_NODES.length-1,i+2)];
  return {x:catmull(a[0],b[0],c[0],d[0],f),y:b[1]+(c[1]-b[1])*f,z:catmull(a[2],b[2],c[2],d[2],f),width:b[3]+(c[3]-b[3])*f};
}
const samples=Array.from({length:157},(_,i)=>riverPoint(i/156));
export function watercourse(x,z){
  if(x< -55||x>72||z< -66||z>46)return {distance:Infinity,y:0,width:0};
  let result={distance:Infinity,y:0,width:0};
  for(let i=0;i<samples.length-1;i++){
    const a=samples[i],b=samples[i+1],dx=b.x-a.x,dz=b.z-a.z;
    const t=Math.max(0,Math.min(1,((x-a.x)*dx+(z-a.z)*dz)/(dx*dx+dz*dz)));
    const distance=Math.hypot(x-a.x-t*dx,z-a.z-t*dz);
    if(distance<result.distance)result={distance,y:a.y+(b.y-a.y)*t,width:a.width+(b.width-a.width)*t};
  }
  return result;
}
export function lawnWeight(x,z){
  let weight=0;
  for(const a of LAWNS){const r=Math.hypot((x-a.x)/a.rx,(z-a.z)/a.rz);weight=Math.max(weight,Math.max(0,Math.min(1,(1-r)*7)));}
  return weight;
}
