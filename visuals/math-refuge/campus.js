import * as THREE from 'three';
import {createLectern} from './lectern.js?v=38-board-tone';
import {createUpperLounge} from './upper-lounge.js?v=42-warm-seating';
import {perimeterRails} from './upper-guards.js?v=36-board-detail';
import {createAutomaticDoors} from './automatic-doors.js?v=39-full-height-doors';
import {BUILDING_SCALE as S,DECK_Y,HALL,COURT_DECKS,SEA_TERRACE,COFFEE_PAD,BRIDGES,GARDEN_PADS,GIANT_TREES,ORNAMENTAL_TREES,SEAT_ROWS,SEAT_COLUMNS} from './site-layout.js?v=36-board-detail';
import {seaLevel} from './landscape-shape.js?v=36-board-detail';
import {curvedSeatBack,terraceStoneMap} from './auditorium-furniture.js?v=15-fixed-hall';

// Architectural geometry for dry offshore decks, rooms and supported inter-storey stairs.
// No swimming basin or exposed support piles are constructed.
export function createCampus(scene,{box,soft,beam,floor,glazing,railing,sofa,table,planter,instance,cylinder,materials}){
  const {steel,stone,edge,brass,timber,pale,darkFabric,soil,glass,light,blackboard}=materials;
  const shell=new THREE.MeshStandardMaterial({color:'#544e45',roughness:.85,metalness:.02,envMapIntensity:.3});
  const seatCloth=new THREE.MeshStandardMaterial({color:'#776352',roughness:.97,normalMap:pale.normalMap,roughnessMap:pale.roughnessMap});
  const meta=(name,data)=>{const o=new THREE.Object3D();o.name=name;o.userData=data;scene.add(o);return o;};
  const railJoint=new THREE.SphereGeometry(1,12,8),railAnchors=new Set(),joints=new Set();
  // Rails and posts use the very same anchors, so every rail meets a post and
  // every post lands on a tread or landing, including the changes of slope.
  function supportedRail(name,anchors){
    const height=.95/S,tops=anchors.map(p=>[p[0],p[1]+height,p[2]]);
    for(const [i,p] of anchors.entries()){
      const key=p.map(v=>v.toFixed(5)).join(',');
      if(!railAnchors.has(key)){railAnchors.add(key);box([p[0],p[1]+.012,p[2]],[.105,.024,.105],steel);beam(p,tops[i],.018/S,brass);}
      for(const fraction of [1,.48]){
        const radius=(fraction===1?.025:.018)/S,jointKey=key+':'+fraction;
        if(!joints.has(jointKey)){joints.add(jointKey);instance(railJoint,brass,[p[0],p[1]+height*fraction,p[2]],[radius,radius,radius]);}
      }
      if(i)for(const fraction of [1,.48])beam(
        [anchors[i-1][0],anchors[i-1][1]+height*fraction,anchors[i-1][2]],
        [p[0],p[1]+height*fraction,p[2]],fraction===1?.025/S:.012/S,brass);
    }
    meta(name,{anchors,tops,height,basePlates:true,continuousJoints:true});
  }
  function guardTerrace(name,rectangles,y,openings=[]){
    const segments=perimeterRails(rectangles,openings),height=.95/S;
    for(const [index,[a,b,c,d]] of segments.entries()){
      const length=Math.hypot(c-a,d-b),count=Math.max(1,Math.ceil(length/1.3));
      const anchors=Array.from({length:count+1},(_,i)=>[a+(c-a)*i/count,y,b+(d-b)*i/count]);
      supportedRail(name+' edge '+index,anchors);
      for(let i=0;i<count;i++){
        const p=anchors[i],q=anchors[i+1],width=length/count-.02;
        box([(p[0]+q[0])/2,y+height*.48,(p[2]+q[2])/2],a===c?[.024,height*.80,width]:[width,height*.80,.024],glass);
      }
    }
    meta(name,{rectangles,segments,openings,height,completePerimeter:true});
  }
  function supportedFlight(name,x,startZ,count,tread,rise,width,landingZ){
    const top=i=>DECK_Y+rise*(i+1)/count,lastZ=startZ-(count-1)*tread;
    for(const sign of [-1,1]){
      const railX=x+sign*(width/2-.09),anchors=[];
      const stride=Math.max(1,Math.floor(.9/(tread*S)));
      for(let i=0;i<count;i++)if(i%stride===0||i===count-1)anchors.push([railX,top(i),startZ-i*tread]);
      anchors.push([railX,DECK_Y+rise,landingZ]);
      supportedRail(name+' rail '+sign,anchors);
      // Rectangular steel stringers connect tread undersides to both bearings.
      const a=new THREE.Vector3(railX,DECK_Y-.03,startZ+tread/2),b=new THREE.Vector3(railX,DECK_Y+rise-.14,landingZ);
      const direction=b.clone().sub(a),mid=a.clone().add(b).multiplyScalar(.5);
      box(mid.toArray(),[.10,direction.length(),.20],steel,[Math.atan2(direction.z,direction.y),0,0]);
      box([railX,DECK_Y+.02,startZ],[.23,.08,.32],steel);
      box([railX,DECK_Y+rise-.12,landingZ],[.20,.22,.26],steel);
    }
    for(let i=0;i<count;i++)box([x,top(i)-rise/count-.025,startZ-i*tread],[width-.10,.06,.13],steel);
    meta(name,{count,x,startZ,lastZ,tread,rise,width,landingZ});
  }
  const lightingZones=[],automaticDoors=createAutomaticDoors(THREE,glass,steel);
  const lampRing=new THREE.TorusGeometry(1,.025,8,64);
  const shade=new THREE.LatheGeometry([new THREE.Vector2(.045,0),new THREE.Vector2(.14,-.035),new THREE.Vector2(.32,-.12),new THREE.Vector2(.48,-.24),new THREE.Vector2(.50,-.27),new THREE.Vector2(.47,-.30)],40);
  const shadeMaterial=new THREE.MeshStandardMaterial({color:'#a6957b',roughness:.5,metalness:.45,side:THREE.DoubleSide});
  function sculptedPendant(x,y,z,r=1){
    instance(shade,shadeMaterial,[x,y,z],[r,r,r]);
    instance(cylinder,light,[x,y-.255*r,z],[.43*r,.015,.43*r]);
    beam([x,y,z],[x,y+.33,z],.009/S,steel);
  }
  const acousticCeiling=new THREE.MeshPhysicalMaterial({color:'#655d50',roughness:1,metalness:0,specularIntensity:0,envMapIntensity:.04,normalMap:pale.normalMap,normalScale:new THREE.Vector2(.08,.08)});
  function linearLamp(x,y,z,length){
    soft([x,y,z],[length,.12/S,.24/S],brass);
    box([x,y-.067/S,z],[length-.12/S,.02/S,.15/S],light);
    for(const side of [-1,1])beam([x+side*length*.35,y,z],[x+side*length*.35,y+.16,z],.008/S,steel);
  }
  function furnishLighting(name,x,z,w,d,y,h){
    const ceiling=y+h,pendant=ceiling-.28;
    let type='recessed linear',gain=.65,color='#ffe1b9';
    if(name==='Academic living villa'){
      type='layered bronze pendants with recessed opal diffusers';
      for(const [dx,dz,r] of [[-1,-1,1.25],[1,.6,.9]])sculptedPendant(x+dx,pendant-.08,z+dz,r);
      for(const [dx,radius] of [[-1,.82],[1,.60]]){
        instance(lampRing,brass,[x+dx,pendant,z],[radius,radius,radius],[Math.PI/2,0,0]);
        instance(lampRing,light,[x+dx,pendant-.045,z],[radius,radius,radius],[Math.PI/2,0,0]);
        for(const side of [-1,1])beam([x+dx+side*radius*.65,pendant,z],[x+dx+side*radius*.65,ceiling,z],.007/S,steel);
      }
      gain=.8;
    }else if(name.startsWith('Quiet residential')){
      type='soft cove and paired bedside lamps';gain=.36;color='#ffdab1';
      for(const side of [-1,1]){
        const bx=x-1+side*.94,bz=z-.2;
        instance(cylinder,brass,[bx,y+.77/S,bz],[.025/S,.58/S,.025/S]);
        instance(cylinder,pale,[bx,y+1.15/S,bz],[.20/S,.24/S,.20/S]);
        instance(cylinder,light,[bx,y+1.025/S,bz],[.16/S,.015/S,.16/S]);
        soft([bx,y+.24/S,bz],[.42/S,.48/S,.42/S],timber);
      }
      for(const side of [-1,1])box([x,ceiling-.04,z+side*(d/2-.3)],[w-.8,.018,.028],light);
    }else if(name==='Independent quiet library'){
      type='three shielded reading pendants and shelf coves';gain=1;
      for(const dx of [-4,4])lightingZones.push({name:'Library reading '+dx,position:[x+dx,pendant-.22,z],target:[x+dx,y+.65,z],gain:.75,color:'#ffecd8',power:250});
      for(const side of [-1,1])box([x,ceiling-.09,z+side*(d/2-.35)],[w-.8,.025,.06],light);
      for(const dx of [-4,0,4])linearLamp(x+dx,pendant,z,1.7);
    }else if(name==='Discussion villa'||name==='Upper small seminar'){
      type='table-centered linear pendant';gain=.7;linearLamp(x,pendant,z,3.2);
    }else if(name==='Upper private studies'){
      type='paired quiet study pendants';for(const dx of [-2,2])linearLamp(x+dx,pendant,z,1.5);
    }else{
      type='recessed service lighting';gain=.65;
      for(const dz of [-1.5,1.5])linearLamp(x,ceiling-.16,z+dz,Math.min(4,w-1));
    }
    meta(name+' light fixtures',{type,color,glareControlled:true});
    // Every occupied room receives actual illumination, including upstairs.
    lightingZones.push({name,position:[x,pendant-.22,z],target:[x,y+.45,z],gain,color,power:name.startsWith('Quiet')?130:240});
  }
  function books(cx,y,z,w){
    box([cx,y+1.08,z],[w,2.16,.32],timber);
    for(let row=0;row<4;row++){
      box([cx,y+.12+row*.52,z+.12],[w,.045,.38],brass);
      for(let i=0;i<Math.floor(w/.19);i++)box([cx-w/2+.14+i*.19,y+.32+row*.52,z+.13],[.12,.26+(i%3)*.06,.25],i%3?blackboard:pale);
    }
  }
  function room(name,cx,cz,w,d,clear=3.2,base=0,doors=['south'],ownFloor=true,ownRoof=true){
    const y=base+DECK_Y,h=clear/S,roof=base+DECK_Y+h+.20;
    if(ownFloor)floor(base,w,d,cx,cz);if(ownRoof)floor(roof,w+.55,d+.55,cx,cz);
    for(const [side,x,z,width,axis] of [['south',cx,cz+d/2,w,'x'],['north',cx,cz-d/2,w,'x'],['west',cx-w/2,cz,d,'z'],['east',cx+w/2,cz,d,'z']]){
      const style=name==='Low sea-facing seminar hall'&&side==='east'?{panels:1,frame:.022/S,seal:.008/S}:undefined;
      if(doors.includes(side)){
        const isHall=name==='Low sea-facing seminar hall',gap=isHall?2.0:1.45,pane=(width-gap)/2;
        const fixedStyle=isHall?{panels:side==='west'?2:1,frame:.022/S,seal:.005/S}:style;
        for(const sign of [-1,1])glazing(x+(axis==='x'?sign*(gap+pane)/2:0),y,z+(axis==='z'?sign*(gap+pane)/2:0),pane,h,axis,fixedStyle);
        if(isHall){
          automaticDoors.add(scene,{x,y,z,width:gap,height:h,handleHeight:1.1/S,axis,name:side});
        }
      }else glazing(x,y,z,width,h,axis,style);
    }
    for(const side of [-1,1]){box([cx,y+h-.12,cz+side*(d/2-.18)],[w-.36,.018,.022],light);box([cx+side*(w/2-.18),y+h-.12,cz],[.022,.018,d-.36],light);}
    if(ownRoof){for(let x=cx-w/2+.35;x<cx+w/2;x+=.65)box([x,y+h-.08,cz],[.09,.10,d-.1],timber);
      furnishLighting(name,cx,cz,w,d,y,h);
    }
    meta(name,{bounds:[cx-w/2,cx+w/2,cz-d/2,cz+d/2],floorY:y,clearHeight:clear,dry:true});
    return roof;
  }
  // Main house wings connect across a continuous, open-to-sky dry courtyard.
  for(const [a,b,c,d] of COURT_DECKS)floor(0,b-a,d-c,(a+b)/2,(c+d)/2);
  floor(0,15,28,-6,0);floor(0,12,28,11.5,0);
  const upper=room('Academic living villa',-6,-4,12,18,3.2,0,['south','west','east'],false);
  const eastUpper=room('Discussion villa',11.5,-4,10,18,3.2,0,['south','west','east'],false);
  room('Upper private studies',-7,-7,9,10,2.8,upper,['south'],false);
  room('Upper small seminar',11,-7,8,10,2.8,eastUpper,['south'],false);
  for(const [x,y] of [[-6,upper+DECK_Y],[11.5,eastUpper+DECK_Y]]){sofa(x-2,y,3);table(x+1,y,3,1.2,.8);}
  books(-6,DECK_Y,-12.65,10);
  sofa(-8,DECK_Y,-5);sofa(-4,DECK_Y,-5);sofa(-8,DECK_Y,0,Math.PI);table(-6,DECK_Y,-2,2.7,1.1);
  table(11,DECK_Y,-4,2.2,1.3);sofa(11,DECK_Y,-7);sofa(11,DECK_Y,-1,Math.PI);
  for(const x of [-9,-5]){table(x,upper+DECK_Y,-8,1.6,.8);sofa(x,upper+DECK_Y,-10);}
  table(11,eastUpper+DECK_Y,-7,2,1.2);sofa(11,eastUpper+DECK_Y,-9);sofa(11,eastUpper+DECK_Y,-5,Math.PI);
  // Exterior stair runs beside the west wing, linked to the lower sea terraces.
  const rise=upper,steps=28;
  for(let i=0;i<steps;i++){box([-12.75,DECK_Y+rise*(i+.5)/steps,12-i*.56],[1.25,rise/steps,.57],timber);box([-12.75,DECK_Y+rise*(i+1)/steps+.005,12-i*.56+.25],[1.10,.012,.018],light);}
  floor(upper,2.2,1.2,-12.25,-3.98);
  supportedFlight('Villa exterior stair',-12.75,12,steps,.56,rise,1.25,-3.98);
  guardTerrace('West villa complete upper guard',[[-12.275,.275,-13.275,5.275],[-13.35,-11.15,-4.58,-3.38]],upper+DECK_Y,[{axis:'x',fixed:-3.38,from:-13.285,to:-12.215}]);
  guardTerrace('East villa complete upper guard',[[6.225,16.775,-13.275,5.275]],eastUpper+DECK_Y);
  for(const x of [-13.1,-11.6])box([x,(DECK_Y+upper)/2,-4.2],[.14,upper-DECK_Y,.14],steel);

  // Quiet, detached library and two compact residential villas landward.
  room('Independent quiet library',-37,-16,13,10,3.0,0,['south','east','west']);
  books(-37,DECK_Y,-20.7,11);
  for(const x of [-41,-37,-33]){table(x,DECK_Y,-16,1.7,.8);sofa(x,DECK_Y,-18);}
  for(const [i,x,z] of [[1,-56,-28],[2,-47,-38]]){
    room('Quiet residential villa '+i,x,z,8,7,2.8,0,['east','west']);
    soft([x-1,DECK_Y+.28,z],[2.0/S,.45/S,2.1/S],pale);sofa(x+1.5,DECK_Y,z-1);
    floor(0,3,7,x+5.5,z);railing(x+7,DECK_Y,z,7,'z');
  }
  room('Service and tea kitchen',-36.5,19,11,8,2.8,0,['west','east']);
  box([-39,DECK_Y+.45,18],[2,.9,5],stone);box([-35,DECK_Y+1,19],[.12,2,7],timber);
  // Dry entry paths connect the rooms and continuous dry courtyard.
  floor(0,47,2.6,-46.5,8);floor(0,2.6,23,-46,-4.8);floor(0,2.5,2.6,-44.75,-16);
  floor(0,2.6,48,-63,-16);floor(0,3,2.6,-61.5,-28);floor(0,12,2.6,-57,-38);
  floor(0,38,2.2,-43,24.5);floor(0,2.2,19,-24,17);
  // Modular offshore garden trays and service spines; seawater stays beneath.
  for(const [a,b,c,d] of GARDEN_PADS){
    box([(a+b)/2,-.4,(c+d)/2],[b-a,.9,d-c],edge);
    box([(a+b)/2,.145,(c+d)/2],[b-a-.12,.19,d-c-.12],materials.leaf);
  }
  meta('Offshore planted garden trays',{bounds:GARDEN_PADS,exposedPiles:false});
  for(const [x,z,species] of ORNAMENTAL_TREES){
    if(x<0)floor(0,3.6,3.6,x,z);
    const w=2.2;box([x,.42,z],[w,.4,w],stone);box([x,.625,z],[w-.35,.025,w-.35],soil);
    for(const sign of [-1,1])box([x+sign*(w/2-.07),.65,z],[.14,.06,w],brass);
    meta('Framed specimen tree '+x+','+z,{x,z,species,exposedSoil:w-.35,planterWidth:w});
  }
  for(const [x,z] of GIANT_TREES){
    box([x,.44,z],[3.8,.4,3.8],stone);box([x,.645,z],[3.35,.025,3.35],soil);
  }
  floor(0,2,17,-63,-43.5);floor(0,8,2,-39,-29);floor(0,2,13,-30,-27);
  floor(0,2,15,-24,32);floor(0,14,2,-37,31);
  for(const [x,z] of [[-70,8],[-63,-53],[-24,40]]){
    floor(0,3,3,x,z);box([x,DECK_Y+.012,z],[1.2,.024,.07],brass);
    meta('Future platform connector '+x+','+z,{x,z,width:3});
  }
  // One small classical garden accent, not the dominant architectural language.
  floor(0,5,5,-35,-29);
  for(const x of [-37,-33])for(const z of [-31,-27])box([x,1.2,z],[.13,2.4,.13],timber);
  for(let i=0;i<8;i++){const w=5.9-i*.63;box([-35,2.5+i*.16,-29],[w,.12,w],edge);}
  table(-35,DECK_Y,-29,1.3,1.3);meta('Bamboo tea pavilion',{x:-35,z:-29});
  soft([-35,2.22,-29],[.38,.12,.38],timber);box([-35,2.15,-29],[.28,.02,.28],light);
  meta('Bamboo tea pavilion light fixtures',{type:'single sheltered warm lantern',glareControlled:true});

  // A supported offshore platform: ocean remains under the hall, not landfill.
  const [tw,te,tn,ts]=SEA_TERRACE,terraceCenter=(tw+te)/2,terraceCenterZ=(tn+ts)/2;
  floor(0,te-tw,ts-tn,terraceCenter,terraceCenterZ);
  // Large-format honed limestone, aligned with the hall and sea edge rather than
  // the generic small-square grid. Restrained variation and 6 mm shadow joints.
  const mineralMap=terraceStoneMap();
  const pavingMaterials=['#736e61','#776f61','#70695b'].map(color=>new THREE.MeshStandardMaterial({color,map:mineralMap,roughness:.96,metalness:0,envMapIntensity:.12,normalMap:stone.normalMap,normalScale:new THREE.Vector2(.025,.025)}));
  const borderMaterial=new THREE.MeshStandardMaterial({color:'#454b47',roughness:.96,metalness:0,envMapIntensity:.1});
  const pavingRects=[[tw+.18,HALL.west,tn+.18,ts-.18],[HALL.east,te-.18,tn+.18,ts-.18],[HALL.west,HALL.east,tn+.18,HALL.north],[HALL.west,HALL.east,HALL.south,ts-.18]];
  let slabCount=0;
  for(const [a,b,c,d] of pavingRects){
    const nx=Math.ceil((b-a)/2.8),nz=Math.ceil((d-c)/1.7),w=(b-a)/nx,h=(d-c)/nz;
    for(let i=0;i<nx;i++)for(let j=0;j<nz;j++){
      box([a+(i+.5)*w,DECK_Y+.004,c+(j+.5)*h],[w-.0045,.014,h-.0045],pavingMaterials[(i*7+j*3+slabCount++)%3]);
    }
  }
  for(const z of [tn+.09,ts-.09])box([terraceCenter,DECK_Y+.006,z],[te-tw-.16,.018,.18],borderMaterial);
  for(const x of [tw+.09,te-.09])box([x,DECK_Y+.006,terraceCenterZ],[.18,.018,ts-tn-.36],borderMaterial);
  // A slim matte champagne threshold defines the entrance, not a shiny grid.
  box([HALL.west-.06,DECK_Y+.012,0],[.025,.012,2.2],brass);
  meta('Honed limestone terrace paving',{slabs:slabCount,jointMetres:.0045*S,rectangles:pavingRects,roughness:.96,largeFormat:true});
  meta('Expanded sea lounge terrace',{bounds:SEA_TERRACE,eastClearance:te-HALL.east,pool:false,heightAboveSea:(DECK_Y-seaLevel)*S});
  // An open view corridor: only a low roofed link, not a tall structure.
  const canopyStart=24.5,canopyEnd=HALL.west+.02;
  box([(canopyStart+canopyEnd)/2,2.55,0],[canopyEnd-canopyStart,.13,2.4],edge);
  for(const x of [25,29.5,34.4])for(const z of [-1.1,1.1])box([x,1.3,z],[.09,2.6,.09],steel);
  meta('Aligned rear entrance canopy',{startX:canopyStart,endX:canopyEnd,centerZ:0,bridgeZ:BRIDGES[1].z,doorZ:0});
  const cx=(HALL.west+HALL.east)/2,cz=0,hallDepth=HALL.south-HALL.north;
  room('Low sea-facing seminar hall',cx,cz,HALL.east-HALL.west,HALL.south-HALL.north,HALL.clearHeight,0,['west','north','south'],false,false);
  const carpetMaterial=new THREE.MeshStandardMaterial({color:'#9d8d79',roughness:1,metalness:0,envMapIntensity:.08,normalMap:pale.normalMap,normalScale:new THREE.Vector2(.12,.12),roughnessMap:pale.roughnessMap});
  const tierCarpets=['#7d6e5c','#8e7e6a'].map(color=>{const material=carpetMaterial.clone();material.color.set(color);return material;});
  const carpet=new THREE.Mesh(new THREE.BoxGeometry(HALL.east-HALL.west-.16,.024,HALL.south-HALL.north-.16),carpetMaterial);
  carpet.name='Warm woven seminar carpet';carpet.position.set(cx,DECK_Y+.016,0);carpet.receiveShadow=true;scene.add(carpet);
  // Fixed two-storey hall: the ground floor keeps its board clearance.
  const hallUpper=DECK_Y+HALL.clearHeight/S+.20;
  floor(hallUpper,8.95,20.55,cx,0);
  room('Upper seminar lounge',cx,0,7,13,2.8,hallUpper,['west','south'],false,true);

  const upperLounge=createUpperLounge(THREE,{seatCloth,seatShell:shell,seatMetal:brass});
  upperLounge.group.position.set(cx,hallUpper+DECK_Y,0);upperLounge.group.scale.setScalar(1/S);scene.add(upperLounge.group);
  const ceiling=new THREE.Mesh(new THREE.BoxGeometry(8.1,.04,19.4),acousticCeiling);
  ceiling.position.set(cx,DECK_Y+HALL.clearHeight/S,0);ceiling.receiveShadow=true;ceiling.name='Fixed seminar acoustic ceiling';scene.add(ceiling);
  // Selected concept A: one low suspended oval, clear of the task lighting.
  const pendant=new THREE.Group();pendant.name='Floating oval seminar pendant';pendant.position.set(37.4,DECK_Y+HALL.clearHeight/S-.45,0);scene.add(pendant);
  const ovalGeometries=[];
  function ovalBand(rx,rz,width,depth,material,dy){
    const shape=new THREE.Shape();shape.absellipse(0,0,rx,rz,0,Math.PI*2,false,0);
    const hole=new THREE.Path();hole.absellipse(0,0,rx-width,rz-width,0,Math.PI*2,true,0);shape.holes.push(hole);
    const geometry=new THREE.ExtrudeGeometry(shape,{depth,bevelEnabled:false,steps:1,curveSegments:80});ovalGeometries.push(geometry);
    const mesh=new THREE.Mesh(geometry,material);mesh.rotation.x=Math.PI/2;mesh.position.y=dy;pendant.add(mesh);
  }
  ovalBand(1.55,5.5,.075,.09,brass,0);ovalBand(1.532,5.482,.037,.008,light,-.091);
  for(const angle of [Math.PI/4,Math.PI*3/4,Math.PI*5/4,Math.PI*7/4]){
    const x=37.4+1.51*Math.cos(angle),z=5.46*Math.sin(angle);
    beam([x,pendant.position.y,z],[x,DECK_Y+HALL.clearHeight/S-.035,z],.006/S,steel);
  }
  pendant.userData={concept:'A',radii:[1.55,5.5],taskLightClearance:HALL.boardX-1.05-(37.4+1.55),suspensions:4};
  for(const z of [-4.5,4.5])lightingZones.push({name:'Seminar downlight '+z,position:[cx,DECK_Y+HALL.clearHeight/S-.35,z],target:[cx,DECK_Y,z],gain:1,color:'#ffe8cf',power:220});
  // Recessed asymmetric wall-wash bars sit ahead of the boards, above eye level.
  // Separate lighting circuits keep the chalk visible without brightening the glass.
  for(const z of [-3,0,3]){
    const x=HALL.boardX-1.05,y=DECK_Y+HALL.clearHeight/S-.18;
    soft([x,y,z],[.22,.12,2.8],steel);
    box([x+.045,y-.069,z],[.075,.012,2.55],light);
    lightingZones.push({name:'Blackboard wall wash '+z,position:[x,y-.16,z],target:[HALL.boardX,DECK_Y+1.8,z],gain:1,color:'#fff0dc',power:90,range:7,angle:Math.PI*.4,task:'blackboard'});
  }
  // Low-contrast reflected fill reaches chair sides and undersides, where the
  // ceiling spots cannot. Finite range confines this shadow-free bounce to the hall.
  for(const x of [37,41])for(const z of [-6.8,6.8]){
    lightingZones.push({name:`Seminar indirect fill ${x} ${z}`,type:'point',position:[x,DECK_Y+2.35/S,z],gain:1,color:'#f9e8d5',power:65,range:11,task:'seminar-fill'});
  }
  meta('Seminar indirect lighting',{circuits:4,shadowFree:true,local:true});
  meta('Blackboard dedicated lighting',{circuits:3,independentOfTour:true,shielded:true,colorTemperature:3500});
  const n=34,stairX=33.3,stairStart=9.6,landingCenter=0,stairTread=.251;
  for(let i=0;i<n;i++){box([stairX,DECK_Y+hallUpper*(i+.5)/n,stairStart-i*stairTread],[1.3,hallUpper/n,stairTread+.005],timber);box([stairX,DECK_Y+hallUpper*(i+1)/n+.005,stairStart-i*stairTread+stairTread/2-.02],[1.14,.012,.018],light);}
  floor(hallUpper,3.8,2.4,34.4,landingCenter);
  supportedFlight('Hall exterior stair',stairX,stairStart,n,stairTread,hallUpper,1.3,landingCenter+.9);
  guardTerrace('Hall complete upper guard',[[34.525,43.475,-10.275,10.275],[32.5,36.3,landingCenter-1.2,landingCenter+1.2]],hallUpper+DECK_Y,[{axis:'x',fixed:landingCenter+1.2,from:32.74,to:33.86}]);
  // Thin horizontal cantilever beams tie into the upper slab; no columns below
  // the landing obstruct the centered ground-floor approach.
  for(const z of [landingCenter-.9,landingCenter+.9])box([34.4,DECK_Y+hallUpper-.10,z],[3.65,.18,.12],steel);
  meta('Centered upper hall entrance',{doorCenterZ:0,landingCenterZ:landingCenter,landingBounds:[32.5,36.3,-1.2,1.2],supportColumns:0,cantileverBeams:2,treadMetres:stairTread*S});
  meta('Two-storey seminar hall',{storeys:2,upperFloor:hallUpper+DECK_Y,fixedRoof:true,stairSteps:n,riserMetres:hallUpper/n*S});
  meta('Seminar hall light fixtures',{type:'shielded bronze linear pendants, warm seat lighting and dedicated board wall wash',glareControlled:true});
  meta('Seamless smart seminar glazing',{panels:1,joints:0,sealMetres:0,frameMetres:.022,touchLanguage:true});
  // A small independent coffee cabin on the north platform.
  const [cw,ce,cn,cs]=COFFEE_PAD;floor(0,ce-cw,cs-cn,(cw+ce)/2,(cn+cs)/2);
  room('North coffee cabin',39,-22,6,6,2.9,0,['south'],false,true);
  box([39,DECK_Y+.48,-23.6],[3.8,.96,1],timber);
  box([39,DECK_Y+.99,-23.6],[3.95,.07,1.08],stone);
  const machine=new THREE.Group();machine.name='Coffee machine';machine.position.set(39,DECK_Y+1.03,-23.6);scene.add(machine);
  const coffeeMaterial=new THREE.MeshStandardMaterial({color:'#343634',roughness:.72,metalness:.25});
  const part=(p,size,material)=>{const m=new THREE.Mesh(new THREE.BoxGeometry(...size),material);m.position.fromArray(p);machine.add(m);};
  part([0,.30,0],[.86,.60,.55],coffeeMaterial);part([0,.04,.23],[.94,.08,.7],steel);
  part([0,.5,.285],[.72,.14,.025],blackboard);
  for(const x of [-.23,.23]){
    part([x,.25,.40],[.075,.07,.30],brass);
    const cup=new THREE.Mesh(new THREE.CylinderGeometry(.10,.075,.15,16),shell);cup.position.set(x,.145,.39);machine.add(cup);
    const bean=new THREE.Mesh(new THREE.CylinderGeometry(.12,.08,.22,12),timber);bean.position.set(x,.70,0);machine.add(bean);
  }
  machine.userData={groupHeads:2,cups:2,hoppers:2};
  table(38,DECK_Y,-21,1.3,.75);sofa(36.9,DECK_Y,-21,Math.PI/2);
  meta('North coffee cabin amenities',{coffeeMachine:true,counter:true,seating:true});
  for(const [index,bridge] of BRIDGES.entries()){
    const {x,z,axis,span,width,rise}=bridge,steps=28;
    const point=(t,y)=>[x+(axis==='x'?(t-.5)*span:0),y,z+(axis==='z'?(t-.5)*span:0)];
    for(let i=0;i<steps;i++){
      const t=(i+.5)/steps,y=DECK_Y+rise*Math.sin(Math.PI*t);
      const slope=rise*Math.PI/span*Math.cos(Math.PI*t);
      box(point(t,y-.04),axis==='x'?[span/steps+.006,.08,width]:[width,.08,span/steps+.006],timber,axis==='x'?[0,0,Math.atan(slope)]:[-Math.atan(slope),0,0]);
      for(const sign of [-1,1]){
        const a=point(i/steps,DECK_Y+rise*Math.sin(Math.PI*i/steps)+.9/S),b=point((i+1)/steps,DECK_Y+rise*Math.sin(Math.PI*(i+1)/steps)+.9/S);
        a[axis==='x'?2:0]+=sign*width/2;b[axis==='x'?2:0]+=sign*width/2;beam(a,b,.018,brass);
      }
    }
    for(let i=0;i<=6;i++)for(const sign of [-1,1]){
      const p=point(i/6,DECK_Y+rise*Math.sin(Math.PI*i/6));p[axis==='x'?2:0]+=sign*width/2;beam(p,[p[0],p[1]+.9/S,p[2]],.014,brass);
    }
    meta('Module arch bridge '+(index+1),bridge);
  }
  // Both sides remain transparent. Acoustic absorption is on the carpet and
  // ceiling, not an opaque north wall blocking the left-hand sea view.
  meta('Transparent seminar side elevations',{northOpaqueWall:false,southOpaqueWall:false});
  const seating=meta('Mathematics auditorium seating',{seats:SEAT_ROWS.length*SEAT_COLUMNS.length,seatsPerRow:SEAT_COLUMNS.length,rows:3,centralAisle:1.6,facing:[1,0,0],seatPositions:[],rowRises:SEAT_ROWS.map(r=>r.rise),clearHeight:HALL.clearHeight,offshore:true});
  const carpetTop=DECK_Y+.028;
  // Two low carpeted seating tiers; the front row stays on the main floor.
  for(const [i,a,b] of [[0,34.95,36.95],[1,36.95,38.45]]){
    const rise=SEAT_ROWS[i].rise/S;
    for(const sign of [-1,1]){
      const riser=new THREE.Mesh(new THREE.BoxGeometry(b-a,rise,9.05),tierCarpets[i]);
      riser.name='Carpeted seating tier '+i+' '+sign;riser.position.set((a+b)/2,carpetTop+rise/2,sign*5.325);
      riser.receiveShadow=true;scene.add(riser);
    }
  }
  // Four 9 cm entry steps, then two 9 cm descents between successive rows.
  // All heights below are metres before conversion to plan coordinates.
  const aisleRuns=[[34.95,35.15,.09],[35.15,35.35,.18],[35.35,35.55,.27],[35.55,36.70,.36],[36.70,37.0,.27],[37.0,38.20,.18],[38.20,38.5,.09]];
  for(const [a,b,height] of aisleRuns){
    box([(a+b)/2,carpetTop+height/(2*S),0],[b-a,height/S,1.6],height>.18?tierCarpets[0]:tierCarpets[1]);
    box([a+.012,carpetTop+height/S+.002,0],[.024,.004,1.6],darkFabric);
  }
  meta('Central carpeted stair aisle',{width:1.6,stepHeightMetres:.09,runs:aisleRuns});
  const curvedShell=curvedSeatBack(),curvedCloth=curvedSeatBack(true),headrest=curvedSeatBack(true,true);
  function chair(x,z,rise,index){
    const angle=Math.PI/2,base=carpetTop+rise/S;
    const pos=p=>new THREE.Vector3(...p).divideScalar(S).applyAxisAngle(new THREE.Vector3(0,1,0),angle).add(new THREE.Vector3(x,base,z)).toArray();
    const part=(p,size,m,round=false,tilt=0)=>{
      const orientation=new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(0,1,0),angle)
        .multiply(new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(1,0,0),tilt));
      const rotation=new THREE.Euler().setFromQuaternion(orientation);
      return (round?soft:box)(pos(p),size.map(v=>v/S),m,[rotation.x,rotation.y,rotation.z]);
    };
    part([0,.025,0],[.62,.045,.72],brass);
    beam(pos([0,.055,.15]),pos([0,.44,-.12]),.04/S,brass);
    part([0,.45,.03],[1.04,.11,.83],shell,true);part([0,.53,.06],[.96,.18,.77],seatCloth,true,.035);
    instance(curvedShell,shell,[x,base,z],[1/S,1/S,1/S],[0,angle,0]);
    instance(curvedCloth,seatCloth,[x,base,z],[1/S,1/S,1/S],[0,angle,0]);
    instance(headrest,seatCloth,[x,base,z],[1/S,1/S,1/S],[0,angle,0]);
    for(const sign of [-1,1]){part([sign*.51,.70,0],[.055,.065,.56],brass);part([sign*.51,.75,.04],[.12,.11,.51],seatCloth,true);}
    part([.57,.79,index%4===0?.28:-.07],index%4===0?[.48,.04,.32]:[.035,.30,.32],timber,true);
    seating.userData.seatPositions.push([x,base,z]);
  }
  for(const [row,{x,rise}] of SEAT_ROWS.entries())for(const [i,z] of SEAT_COLUMNS.entries())chair(x,z,rise,row*SEAT_COLUMNS.length+i);
  const lectern=createLectern(THREE);
  lectern.group.position.set(41.3,DECK_Y+.028,6.5);
  lectern.group.scale.setScalar(1/S);lectern.group.rotation.y=Math.PI/2;scene.add(lectern.group);
  // Operable blackout layer, separate from glazing and opaque chalkboards.
  const blind=new THREE.Mesh(new THREE.BoxGeometry(.008,HALL.clearHeight/S,hallDepth-.6),new THREE.MeshStandardMaterial({color:'#293530',roughness:1}));
  // Keep the optional blind on the sea side, clear of the flush-mounted boards.
  blind.name='East teaching blackout shade';blind.position.set(HALL.east+.029,DECK_Y+HALL.clearHeight/(2*S),0);blind.visible=false;scene.add(blind);
  box([HALL.east+.04,DECK_Y+HALL.clearHeight/S-.04,0],[.04,.12,hallDepth-.6],steel);
  // No sun loungers remain on the compact sea terrace.
  for(const z of [-11,13]){sofa(48,DECK_Y,z,Math.PI/2);table(49.2,DECK_Y,z,1,.7);}
  // Sea access has been removed; the continuous platform fascia and edge lights
  // follow the same complete perimeter without stair projections.
  return {blind,seating,lightingZones,automaticDoors,lectern,
    setTeachingShade(closed){blind.visible=Boolean(closed);},
    dispose(){lectern.dispose();upperLounge.dispose();ovalGeometries.forEach(g=>g.dispose());railJoint.dispose();automaticDoors.dispose();shade.dispose();shadeMaterial.dispose();coffeeMaterial.dispose();machine.traverse(o=>o.geometry?.dispose());lampRing.dispose();acousticCeiling.dispose();headrest.dispose();tierCarpets.forEach(m=>m.dispose());mineralMap.dispose();pavingMaterials.forEach(m=>m.dispose());borderMaterial.dispose();curvedShell.dispose();curvedCloth.dispose();carpet.geometry.dispose();carpetMaterial.dispose();seatCloth.dispose();shell.dispose();}
  };
}
