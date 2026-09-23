import {BUILDING_SCALE as S,DECK_Y,HALL} from './site-layout.js?v44-hall-clearance';
import {SEMINAR,seminarFloor} from './seminar-layout.js?v52-km-rooms';
// Room membership follows the camera eye, not the last navigation button.
export function teachingRoomAt({x,y,z}){
 const inside=(west,east,north,south,floor,height)=>x>west*S&&x<east*S&&z>north*S&&z<south*S&&y>floor*S&&y<(floor*S+height);
 if(inside(HALL.west,HALL.east,HALL.north,HALL.south,DECK_Y,HALL.clearHeight))return 0;
 for(let level=0;level<3;level++)if(inside(SEMINAR.west,SEMINAR.east,SEMINAR.north,SEMINAR.south,seminarFloor(level),SEMINAR.clearHeight))return level+1;
 return -1;
}
