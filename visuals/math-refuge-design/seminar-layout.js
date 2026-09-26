import {BUILDING_SCALE as S,DECK_Y} from './site-layout.js?v44-hall-clearance';
export const SEMINAR={west:-88,east:-80,north:2,south:14,boardX:-80.5,centerZ:8,storeys:3,clearHeight:3.8,storeyHeight:4.15,scale:.52,deck:[-95,-76,-1,18]};
export const seminarFloor=level=>DECK_Y+level*SEMINAR.storeyHeight/S;
export function configureSeminarRoot(root,level){
  root.scale.setScalar(SEMINAR.scale);root.rotation.y=-Math.PI/2;
  root.position.set(SEMINAR.boardX*S-10.4*SEMINAR.scale,seminarFloor(level)*S+.85,SEMINAR.centerZ*S-28*SEMINAR.scale);
}
export const seminarViewOffset=distance=>[-distance*SEMINAR.scale,0,0];
export const seminarArrival={position:[-69,13,29].map(x=>x*S),target:[-84,5.3,8].map(x=>x*S)};
