import * as T from '../3d/vendor/three.module.js';
import {BUILDING_SCALE as S,DECK_Y,LECTERN_SHAFT_PLAN} from './site-layout.js';
const ease=t=>{t=T.MathUtils.clamp(t,0,1);return t*t*t*(t*(t*6-15)+10);};
export function createLecternLift(scene,lectern,material,offset){
 const [a,b,c,d]=LECTERN_SHAFT_PLAN,top=(DECK_Y+.028)*S;
 const lid=new T.Mesh(new T.BoxGeometry((b-a)*S,.024*S,(d-c)*S),material);
 lid.name='Seamless retractable lectern floor lid';lid.receiveShadow=true;
 const x=(a+b)/2*S+offset.x,z=(c+d)/2*S+offset.z,y=top-.012*S;
 lid.position.set(x,y,z);scene.add(lid);
 const baseY=lectern.group.position.y;
 let progress=0,target=0;
 function update(dt){
  progress=T.MathUtils.clamp(progress+Math.sign(target-progress)*Math.min(Math.abs(target-progress),Math.max(0,dt)/5),0,1);
  // First lower the furniture completely; only then slide the flush floor shut.
  const drop=ease(progress/.72),closure=ease((progress-.72)/.28);
  lectern.group.position.y=baseY-1.85*drop;
  lid.position.set(x-((b-a)*S+.06)*(1-closure),y-.055*(1-closure),z);
  lectern.group.userData.liftProgress=progress;
 }
 update(0);
 return {get lowered(){return target===1;},get moving(){return progress!==target;},toggle(){target=1-target;},update};
}
