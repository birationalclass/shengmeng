import {BUILDING_SCALE as S,HALL} from './site-layout.js';
import {bedHeight,branchPoint} from '../ocean/elliptic-model.js';
// Campus coordinates stay local to keep interiors and authored camera paths exact.
// The hall centre is the kilometre-coordinate anchor (2, 0).
export const CAMPUS_ANCHOR=(HALL.west+HALL.east)*.5*S;
export const COAST_LIFT=-.65*S-2.55;
// Geographic east is world +X; north is world -Z (mathematical +Y).
// Only translate the coast; never rotate geography to fit the buildings.
export const geographicDirectionToCampus=direction=>[...direction];
export const toMathCoordinates=(x,z)=>{const p=toBeach(x,z);return [p[0]/1000,-p[1]/1000];};
export const toBeach=(x,z)=>[2000+(x-CAMPUS_ANCHOR),z];
export const fromBeach=(x,z)=>[CAMPUS_ANCHOR+x-2000,z];
export function branchCentre(z){
 let lo=0,hi=1.7;for(let i=0;i<40;i++){const t=(lo+hi)/2;if(Math.abs(branchPoint(t)[1])<Math.abs(z))lo=t;else hi=t;}
 return branchPoint((lo+hi)/2)[0];
}
export function beachDistance(x,z){
 // Segment samples are for navigation/audio only; rendering uses 01's distance map.
 let best=Infinity;
 for(const points of coastSegments){for(let i=1;i<points.length;i++){
  const a=points[i-1],b=points[i],dx=b[0]-a[0],dz=b[1]-a[1];
  const t=Math.max(0,Math.min(1,((x-a[0])*dx+(z-a[1])*dz)/(dx*dx+dz*dz)));
  best=Math.min(best,Math.hypot(x-a[0]-t*dx,z-a[1]-t*dz));
 }}return best;
}
import {ringPoint} from '../ocean/elliptic-model.js';
const coastSegments=[Array.from({length:721},(_,i)=>ringPoint(i*2*Math.PI/720)),Array.from({length:1801},(_,i)=>branchPoint(-1.7+3.4*i/1800))];
export function campusGround(x,z){const p=toBeach(x,z);return bedHeight(beachDistance(...p),...p)+COAST_LIFT;}
export const RESIDENCE_COAST_Z=1250;
export const RESIDENCE_COAST_X=fromBeach(branchCentre(RESIDENCE_COAST_Z),RESIDENCE_COAST_Z)[0];
