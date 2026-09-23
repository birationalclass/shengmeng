import {createLectern} from './lectern.js?v62-chalk-ink';
import * as THREE from 'three';
import {createRoofNumber} from './roof-number.js?v62-chalk-ink';
import {BUILDING_SCALE as S,DECK_Y} from './site-layout.js?v44-hall-clearance';
import {SEMINAR as B,seminarFloor} from './seminar-layout.js?v53-section-sessions';
import {curvedSeatBack} from './auditorium-furniture.js?v=15-fixed-hall';

export function createSeminarBuilding(scene,{box,soft,beam,floor,glazing,instance,materials,automaticDoors}){
  const {steel,stone,brass,timber,pale,light}=materials;
  const cloth=new THREE.MeshStandardMaterial({color:'#847b66',roughness:1});
  const carpet=new THREE.MeshStandardMaterial({color:'#aaa18c',roughness:1});
  const shell=new THREE.MeshStandardMaterial({color:'#615b50',roughness:.85});
  const back=curvedSeatBack(),cushion=curvedSeatBack(true);
  const meta=(name,data)=>{const o=new THREE.Object3D();o.name=name;o.userData=data;scene.add(o);return o;};
  const [w,e,n,s]=B.deck;floor(0,e-w,s-n,(w+e)/2,(n+s)/2);
  floor(0,8,2.6,-73,8); // Connect the existing west expansion jetty.
  const zones=[],blinds=[],seats=[],lecterns=[];
  function rail(anchors){
    for(let i=0;i<anchors.length;i++){
      const p=anchors[i],q=[p[0],p[1]+.95/S,p[2]];
      box([p[0],p[1]+.01,p[2]],[.10,.025,.10],steel);beam(p,q,.018/S,brass);
      if(i)for(const f of [.5,1])beam([anchors[i-1][0],anchors[i-1][1]+.95/S*f,anchors[i-1][2]],[p[0],p[1]+.95/S*f,p[2]],.02/S,brass);
    }
  }
  function flight(x,z0,z1,y0,y1){
    const count=13,tread=(z1-z0)/count,rise=(y1-y0)/count,width=1.35;
    for(let i=0;i<count;i++){
      const z=z0+(i+.5)*tread,y=y0+(i+1)*rise;
      box([x,y-rise/2,z],[width,rise,Math.abs(tread)+.004],timber);
      box([x,y+.006,z+tread*.42],[width-.12,.012,.022],light);
    }
    for(const sign of [-1,1]){
      const rx=x+sign*.59,anchors=Array.from({length:8},(_,j)=>{const i=Math.min(12,j*2);return [rx,y0+(i+1)*rise,z0+(i+.5)*tread];});
      anchors.push([rx,y1,z1]);rail(anchors);
      beam([rx,y0-.06,z0],[rx,y1-.08,z1],.055,steel);
    }
    meta('Seminar supported stair flight',{x,z0,z1,y0,y1,count,riser:rise*S,tread:Math.abs(tread)*S});
  }
  for(let level=0;level<3;level++){
    const base=level*B.storeyHeight/S,y=seminarFloor(level),ceiling=y+B.clearHeight/S;
    if(level)box([-84,y-.08/S,8],[8.4,.16/S,12.4],stone);
    // Four-pane front, quiet timber soffits and an open entrance on the west.
    glazing(B.east,y,8,12,B.clearHeight/S,'z',{panels:1,spacing:12,frame:.022/S,seal:.008/S});
    for(const z of [B.north,B.south])glazing(-84,y,z,8,B.clearHeight/S,'x');
    for(const z of [4.6,11.4])glazing(B.west,y,z,5.2,B.clearHeight/S,'z');
    box([-84,y+.012,8],[7.8,.02,11.8],carpet);
    for(const x of [B.west,B.east])for(const z of (x===B.west?[2,7.2,8.8,14]:[2,8,14]))box([x,y+B.clearHeight/(2*S),z],[.12,B.clearHeight/S,.12],steel);
    box([-84,ceiling,8],[8,.055,12],pale);
    for(const z of [2.2,13.8])box([-84,ceiling-.05,z],[7.6,.025,.035],light);
    for(const x of [-87.8,-80.2])box([x,ceiling-.05,8],[.035,.025,11.6],light);
    for(const z of [5,11]){
      soft([-84,ceiling-.18,z],[4.4,.08,.16],brass);
      box([-84,ceiling-.227,z],[4.25,.012,.12],light);
      for(const dx of [-1.5,1.5])beam([-84+dx,ceiling-.18,z],[-84+dx,ceiling,z],.008,steel);
    }
    soft([B.boardX-.7,ceiling-.13,8],[.16,.08,8.4],brass);
    box([B.boardX-.65,ceiling-.176,8],[.06,.012,8.1],light);
    zones.push({name:'Discussion classroom '+(level+1),position:[-83.5,ceiling-.35,8],target:[B.boardX,y+1.2,8],gain:1,color:'#fff0da',power:220,range:12,angle:Math.PI*.44,task:'seminar-classroom'});
    const positions=[];
    for(const x of [-86.5,-84.8])for(const dz of [-3,-2,-1,1,2,3]){
      const z=8+dz,angle=Math.PI/2;
      const p=(a,b,c)=>[x+c/S,y+b/S,z-a/S];
      soft(p(0,.43,0),[.78/S,.12/S,.94/S],shell);
      soft(p(0,.51,0),[.76/S,.13/S,.90/S],cloth);
      instance(back,shell,[x,y,z],[1/S,1/S,1/S],[0,angle,0]);
      instance(cushion,cloth,[x,y,z],[1/S,1/S,1/S],[0,angle,0]);
      for(const a of [-.46,.46]){
        beam(p(a,.06,.1),p(a,.66,-.05),.025/S,brass);
        soft(p(a,.72,.02),[.50/S,.08/S,.09/S],cloth);
      }
      soft(p(0,.78,.73),[.35/S,.04/S,.9/S],timber);
      beam(p(.4,.05,.7),p(.4,.77,.7),.022/S,steel);positions.push([x,y,z]);
    }
    seats.push(meta('Discussion classroom seats '+(level+1),{rows:2,seats:12,positions,facing:[1,0,0]}));
    const lectern=createLectern(THREE);lectern.group.position.set(-81.9,y+.028,12.8);lectern.group.scale.setScalar(1/S);lectern.group.rotation.y=Math.PI/2;scene.add(lectern.group);lecterns.push(lectern);
    automaticDoors.add(scene,{x:B.west,y,z:8,width:1.6,height:B.clearHeight/S,axis:'z',name:'discussion-'+(level+1)});
    const blind=new THREE.Mesh(new THREE.BoxGeometry(.035,B.clearHeight/S,11.8),new THREE.MeshStandardMaterial({color:'#34463d',roughness:1}));
    blind.name='Discussion classroom shade '+(level+1);blind.position.set(-80.14,y+B.clearHeight/(2*S),8);blind.visible=false;scene.add(blind);blinds.push(blind);
    meta('Discussion classroom '+(level+1),{level,bounds:[B.west,B.east,B.north,B.south],floorY:y,clearHeight:B.clearHeight,rows:2,smartGlassPanels:1});
    // West landing opens directly into the classroom; switchback flights have real bearings.
    floor(base,2.4,13.4,-89,8);
    rail(Array.from({length:4},(_,i)=>[-90.12,y,1.5+i*1.5]));
    rail(Array.from({length:5},(_,i)=>[-90.12,y,8.4+i*1.5]));
    if(level<2){
      const half=B.storeyHeight/(2*S);
      flight(-91.05,6.7,3,y,y+half);
      floor(base+half,3.25,1.4,-91.9,2.45);
      flight(-92.75,3,6.7,y+half,y+2*half);
      floor(base+2*half,4.1,1.2,-91.4,7.25);
      rail([[-93.4,y+2*half,7.85],[-91.5,y+2*half,7.85],[-89.4,y+2*half,7.85]]);
      rail([[-93.4,y+half,1.75],[-91.8,y+half,1.75],[-90.35,y+half,1.75]]);
      // Support mid-landings through to the platform, not to open water.
      for(const x of [-93.3,-90.5])box([x,(DECK_Y+y+half)/2,2.45],[.14,y+half-DECK_Y,.14],steel);
    }
  }
  box([-84.8,seminarFloor(3)-.08/S,8],[10.4,.16/S,14],stone);
  const roofNumber=createRoofNumber(scene,2,-84.8,seminarFloor(3),8,10.4,14);
  meta('Three-storey discussion building',{...B,seatsPerFloor:12,rowsPerFloor:2,connected:true});
  return {lightingZones:zones,blinds,seats,lecterns,dispose(){roofNumber.dispose();lecterns.forEach(l=>l.dispose());back.dispose();cushion.dispose();cloth.dispose();carpet.dispose();shell.dispose();blinds.forEach(b=>{b.geometry.dispose();b.material.dispose();});}};
}
