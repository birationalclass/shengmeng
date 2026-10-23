import * as T from 'three';
import {BUILDING_SCALE as S,HALL,DECK_Y} from './site-layout.js';
import {buildingOffset} from './campus-layout.js';
// Roundoff near a segment endpoint can otherwise produce t > 1 for Three.js.
const ease=t=>Math.max(0,Math.min(1,t*t*t*(10+t*(-15+6*t))));
const v=a=>new T.Vector3(...a),up=new T.Vector3(0,1,0);
const rotation=(eye,target)=>new T.Quaternion().setFromRotationMatrix(new T.Matrix4().lookAt(eye,target,up));
export function classroomBoardPose(aspect=16/9){
 const o=buildingOffset('01B'),target=[HALL.boardX*S+o.x-.03,2.35,o.z];
 const distance=Math.max(3.8,2.2/(2*Math.tan(Math.PI/6))*Math.max(1,2.4/aspect));
 return{position:[target[0]-distance,target[1],target[2]],target,fov:60};
}
// Leave through the existing centre west doorway before rising above the roof.
// Returning samples the same corridor in reverse from the *current* beach pose.
export function createClassroomBeachFlight(board,coast,{returning=false,reduced=false}={}){
 const o=buildingOffset('01B'),west=HALL.west*S+o.x;
 const a=v(board.position),b=v(coast.position),eye=Math.max(DECK_Y*S+1.65,a.y),exit=new T.Vector3(west-4,eye,o.z);
 const inside=new T.CatmullRomCurve3([a,new T.Vector3(Math.min(a.x,west+7),eye,o.z),new T.Vector3(west+1.5,eye,o.z),exit],false,'centripetal');
 const altitude=Math.max(18,Math.min(80,exit.distanceTo(b)*.1));
 const outside=new T.CatmullRomCurve3([exit,new T.Vector3(west-16,Math.max(eye+5,altitude*.45),o.z),new T.Vector3((exit.x+b.x)/2,altitude,(exit.z+b.z)/2),b],false,'centripetal');
 const indoorSeconds=reduced?3:7,outdoorSeconds=reduced?5:11,duration=indoorSeconds+outdoorSeconds;
 const qa=board.quaternion?new T.Quaternion(...board.quaternion):rotation(a,v(board.target)),qb=coast.quaternion?new T.Quaternion(...coast.quaternion):rotation(b,v(coast.target)),door=rotation(exit,new T.Vector3(west-28,eye,o.z));
 const da=Math.max(1,a.distanceTo(v(board.target))),db=Math.max(1,b.distanceTo(v(coast.target)));
 return {duration,door:exit.toArray(),sample(seconds){
  const u=returning?duration-Math.max(0,Math.min(duration,seconds)):Math.max(0,Math.min(duration,seconds));
  const indoor=u<=indoorSeconds,k=ease(indoor?u/indoorSeconds:(u-indoorSeconds)/outdoorSeconds),position=(indoor?inside:outside).getPointAt(k);
  const quaternion=new T.Quaternion().slerpQuaternions(indoor?qa:door,indoor?door:qb,k),distance=indoor?T.MathUtils.lerp(da,25,k):T.MathUtils.lerp(25,db,k);
  const target=position.clone().add(new T.Vector3(0,0,-1).applyQuaternion(quaternion).multiplyScalar(distance));
  const fov=T.MathUtils.lerp(board.fov||60,coast.fov||60,ease(u/duration));
  return{position:position.toArray(),target:target.toArray(),quaternion:quaternion.toArray(),fov,progress:Math.max(0,Math.min(1,seconds/duration))};
 }};
}
