import {HALL,BUILDING_SCALE as S,DECK_Y} from './site-layout.js';

export const HALL_CAMERA_BOUNDS=Object.freeze({
 minX:HALL.west*S+.38,maxX:HALL.boardX*S-.38,
 minY:DECK_Y*S+.65,maxY:DECK_Y*S+HALL.clearHeight-.30,
 minZ:HALL.north*S+.38,maxZ:HALL.south*S-.38
});
const clamp=(v,a,b)=>Math.max(a,Math.min(b,Number.isFinite(v)?v:(a+b)/2));
// Applied after every input and automatic trajectory, before rendering.
export function constrainHallCamera(camera,target){
 const p=camera.position,b=HALL_CAMERA_BOUNDS,before=[p.x,p.y,p.z];
 p.x=clamp(p.x,b.minX,b.maxX);p.y=clamp(p.y,b.minY,b.maxY);p.z=clamp(p.z,b.minZ,b.maxZ);
 const delta=[p.x-before[0],p.y-before[1],p.z-before[2]];
 target.x=clamp(target.x+(Number.isFinite(delta[0])?delta[0]:0),HALL.west*S+.08,HALL.east*S-.08);
 target.y=clamp(target.y+(Number.isFinite(delta[1])?delta[1]:0),DECK_Y*S+.08,DECK_Y*S+HALL.clearHeight-.08);
 target.z=clamp(target.z+(Number.isFinite(delta[2])?delta[2]:0),HALL.north*S+.08,HALL.south*S-.08);
 if(Math.hypot(target.x-p.x,target.y-p.y,target.z-p.z)<.01)target.x=p.x+.08;
 camera.lookAt(target);
 return before.some((v,i)=>v!==[p.x,p.y,p.z][i]);
}
export function hallOverview(aspect=16/9){
 const position=[HALL.west*S+1.5,DECK_Y*S+2.6,0],target=[HALL.boardX*S,DECK_Y*S+2.6,0];
 const fit=2*Math.atan(7.9/((target[0]-position[0])*Math.max(.25,aspect)))*180/Math.PI;
 return{position,target,fov:Math.max(65,Math.min(105,fit))};
}
