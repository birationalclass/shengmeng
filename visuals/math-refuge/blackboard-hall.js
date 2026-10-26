import * as T from 'three';
import {HALL,BUILDING_SCALE as S,DECK_Y,SEAT_ROWS,SEAT_COLUMNS} from './site-layout.js';
import {createSwivelChairs} from './swivel-chairs.js';
import {curvedSeatBack} from './auditorium-furniture.js';
import {createLectern} from './lectern.js';

export const SMART_SCREEN_BACKGROUND='#777b7e';
// This factory constructs only the ground-floor auditorium: no campus or exterior.
export function createBlackboardHall(scene){
 const root=new T.Group();root.name='Blackboard auditorium';root.scale.setScalar(S);scene.add(root);
 const standard=(color,roughness=1,metalness=0)=>new T.MeshStandardMaterial({color,roughness,metalness});
 const carpet=standard('#9d8d79'),wall=standard('#b6b3ac'),ceiling=standard('#777166'),bronze=standard('#aa9270',.55,.48),wood=standard('#655443',.8),shell=standard('#544e45'),cloth=standard('#776352');
 function box(name,p,size,material){const mesh=new T.Mesh(new T.BoxGeometry(...size),material);mesh.name=name;mesh.position.fromArray(p);mesh.castShadow=true;mesh.receiveShadow=true;root.add(mesh);return mesh;}
 const cx=(HALL.west+HALL.east)/2,depth=HALL.south-HALL.north,h=HALL.clearHeight/S,y=DECK_Y;
 box('Auditorium carpet',[cx,y-.04,0],[HALL.east-HALL.west,.08,depth],carpet);
 box('Auditorium acoustic ceiling',[cx,y+h+.035,0],[HALL.east-HALL.west,.07,depth],ceiling);
 for(const z of [HALL.north,HALL.south]){
  box('Auditorium side wall',[cx,y+h/2,z],[HALL.east-HALL.west,h,.08],wall);
  for(const x of [HALL.west+1.1,cx,HALL.east-1.1])box('Vertical acoustic panel',[x,y+h*.5,z+(z<0?.05:-.05)],[.34,h*.72,.025],wood);
 }
 box('Auditorium rear wall',[HALL.west-.035,y+h/2,0],[.07,h,depth],wall);
 const screenMaterial=standard(SMART_SCREEN_BACKGROUND,.96);
 const screen=box('Grey smart screen background',[HALL.east+.03,y+h/2,0],[.06,h,depth],screenMaterial);
 screen.userData.smartScreenBackground=SMART_SCREEN_BACKGROUND;
 for(const z of [HALL.north+.12,HALL.south-.12])box('Smart screen edge',[HALL.east-.014,y+h/2,z],[.04,h,.045],bronze);
 const carpetTop=y+.028,tierOuter=Math.max(...SEAT_COLUMNS.map(Math.abs))+1.05/S,tierInner=.8;
 for(const [i,a,b] of [[0,34.5,36.725+.4/S],[1,36.725+.4/S,38.675+.4/S]])for(const sign of [-1,1]){
  const rise=SEAT_ROWS[i].rise/S;
  box('Carpeted seating tier '+i,[(a+b)/2,carpetTop+rise/2,sign*(tierOuter+tierInner)/2],[b-a,rise,tierOuter-tierInner],carpet);
 }
 const positions=SEAT_ROWS.flatMap(({x,rise})=>SEAT_COLUMNS.map(z=>[x,carpetTop+rise/S,z]));
 const chairs=createSwivelChairs(root,positions,{shell,cloth,metal:bronze,timber:wood,backs:[curvedSeatBack(),curvedSeatBack(true),curvedSeatBack(true,true)],focusX:HALL.boardX},S);
 const lectern=createLectern(T);lectern.group.position.set(41.3,y+.028,6.5);lectern.group.scale.setScalar(1/S);lectern.group.rotation.y=Math.PI/2;root.add(lectern.group);
 const luminous=new T.MeshBasicMaterial({color:'#fff0dc'});
 for(const z of [-6,-3,0,3,6])box('Shielded board light',[HALL.boardX-1.05,y+h-.12,z],[.16,.04,2.5],luminous);
 const oval=new T.Mesh(new T.TorusGeometry(1,.025,10,100),bronze);oval.name='Oval auditorium pendant';oval.rotation.x=Math.PI/2;oval.scale.set(1.55,5.5,1);oval.position.set(37.4,y+h-.45,0);root.add(oval);
 scene.add(new T.HemisphereLight('#fff3df','#66635e',2.1));
 const key=new T.DirectionalLight('#fff0dc',2.5);key.position.set(cx*S,(y+h)*S,0);key.target.position.set(HALL.boardX*S,2.2,0);scene.add(key,key.target);
 const fill=new T.DirectionalLight('#e8eef1',1.1);fill.position.set(HALL.east*S,3,5);fill.target.position.set(HALL.west*S,2,0);scene.add(fill,fill.target);
 return{root,screen,carpetMaterial:carpet,chairs,lectern};
}
