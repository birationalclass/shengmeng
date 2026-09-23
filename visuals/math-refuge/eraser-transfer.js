// Return in free space: leave the board, turn outside the tray, move above it,
// then lower vertically. Pickup follows exactly the reverse path.
export function eraserTransfer(start,rest,t,frontZ){
 const clamp=x=>Math.max(0,Math.min(1,x)),ease=x=>{x=clamp(x);return x*x*(3-2*x);};
 const z=Math.max(frontZ,start.z+.18),hover=rest.y+.35;
 const points=[start,{x:start.x,y:start.y,z},{x:rest.x,y:hover,z},{x:rest.x,y:hover,z:rest.z},rest];
 const times=[0,.22,.68,.85,1];t=clamp(t);let i=0;while(i<3&&t>times[i+1])i++;
 const f=ease((t-times[i])/(times[i+1]-times[i])),a=points[i],b=points[i+1];
 return {x:a.x+(b.x-a.x)*f,y:a.y+(b.y-a.y)*f,z:a.z+(b.z-a.z)*f,rotation:ease((t-.22)/.46)};
}
