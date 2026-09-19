import * as THREE from 'three';
import {BUILDING_SCALE as S,DECK_Y,HALL,COURT_DECK,SEA_TERRACE,SEA_STEPS,GARDEN_PADS,GIANT_TREES,ORNAMENTAL_TREES,SEAT_ROWS,SEAT_COLUMNS} from './site-layout.js?v=14-sea-terraces';
import {seaLevel} from './landscape-shape.js?v=14-sea-terraces';
import {curvedSeatBack,terraceStoneMap} from './auditorium-furniture.js?v=14-sea-terraces';

// Architectural geometry for dry offshore decks, rooms and sea-access stairs.
// No swimming basin or exposed support piles are constructed.
export function createCampus(scene,{box,soft,beam,floor,glazing,railing,sofa,table,planter,instance,cylinder,materials}){
  const {steel,stone,edge,brass,timber,pale,darkFabric,soil,glass,light,blackboard}=materials;
  const shell=new THREE.MeshStandardMaterial({color:'#544e45',roughness:.85,metalness:.02,envMapIntensity:.3});
  const seatCloth=new THREE.MeshStandardMaterial({color:'#776352',roughness:.97,normalMap:pale.normalMap,roughnessMap:pale.roughnessMap});
  const meta=(name,data)=>{const o=new THREE.Object3D();o.name=name;o.userData=data;scene.add(o);return o;};
  const lightingZones=[];
  const lampRing=new THREE.TorusGeometry(1,.025,8,64);
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
      type='double warm ring pendant';
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
      type='three reading pendants';gain=.85;
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
    // The two upstairs rooms use sky/ambient fill plus visible diffusers.
    // Limit direct dynamic sources to eight for the whole campus.
    if(!name.startsWith('Upper'))lightingZones.push({name,position:[x,pendant-.16,z],target:[x,y,z],gain,color});
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
      if(doors.includes(side)){
        const gap=1.45,pane=(width-gap)/2;
        for(const sign of [-1,1])glazing(x+(axis==='x'?sign*(gap+pane)/2:0),y,z+(axis==='z'?sign*(gap+pane)/2:0),pane,h,axis);
      }else glazing(x,y,z,width,h,axis);
    }
    if(ownRoof){for(let x=cx-w/2+.35;x<cx+w/2;x+=.65)box([x,y+h-.08,cz],[.09,.10,d-.1],timber);
      furnishLighting(name,cx,cz,w,d,y,h);
    }
    meta(name,{bounds:[cx-w/2,cx+w/2,cz-d/2,cz+d/2],floorY:y,clearHeight:clear,dry:true});
    return roof;
  }
  // Main house wings connect across a continuous, open-to-sky dry courtyard.
  floor(0,COURT_DECK[1]-COURT_DECK[0],COURT_DECK[3]-COURT_DECK[2],(COURT_DECK[0]+COURT_DECK[1])/2,0);
  floor(0,15,28,-6,0);floor(0,12,28,11.5,0);
  const upper=room('Academic living villa',-6,-4,12,18,3.2,0,['south','west','east'],false);
  const eastUpper=room('Discussion villa',11.5,-4,10,18,3.2,0,['south','west','east'],false);
  room('Upper private studies',-7,-7,9,10,2.8,upper,['south'],false);
  room('Upper small seminar',11,-7,8,10,2.8,eastUpper,['south'],false);
  for(const [x,y] of [[-6,upper+DECK_Y],[11.5,eastUpper+DECK_Y]]){railing(x,y,5,12);sofa(x-2,y,3);table(x+1,y,3,1.2,.8);}
  books(-6,DECK_Y,-12.65,10);
  sofa(-8,DECK_Y,-5);sofa(-4,DECK_Y,-5);sofa(-8,DECK_Y,0,Math.PI);table(-6,DECK_Y,-2,2.7,1.1);
  table(11,DECK_Y,-4,2.2,1.3);sofa(11,DECK_Y,-7);sofa(11,DECK_Y,-1,Math.PI);
  for(const x of [-9,-5]){table(x,upper+DECK_Y,-8,1.6,.8);sofa(x,upper+DECK_Y,-10);}
  table(11,eastUpper+DECK_Y,-7,2,1.2);sofa(11,eastUpper+DECK_Y,-9);sofa(11,eastUpper+DECK_Y,-5,Math.PI);
  // Exterior stair runs beside the west wing, linked to the lower sea terraces.
  const rise=upper,steps=28;
  for(let i=0;i<steps;i++)box([-12.75,DECK_Y+rise*(i+.5)/steps,12-i*.56],[1.25,rise/steps,.57],timber);
  beam([-13.4,DECK_Y+1/S,12],[-13.4,DECK_Y+rise+1/S,12-steps*.56],.025,steel);

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
  floor(0,2,15,-24,32);floor(0,14,2,-37,31);floor(0,20,2,-13,38);
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
  const [tw,te,tn,ts]=SEA_TERRACE,terraceCenter=(tw+te)/2;
  floor(0,te-tw,ts-tn,terraceCenter,0);
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
  for(const x of [tw+.09,te-.09])box([x,DECK_Y+.006,0],[.18,.018,ts-tn-.36],borderMaterial);
  // A slim matte champagne threshold defines the entrance, not a shiny grid.
  box([HALL.west-.06,DECK_Y+.012,0],[.025,.012,2.2],brass);
  meta('Honed limestone terrace paving',{slabs:slabCount,jointMetres:.0045*S,rectangles:pavingRects,roughness:.96,largeFormat:true});
  meta('Expanded sea lounge terrace',{bounds:SEA_TERRACE,eastClearance:te-HALL.east,pool:false,heightAboveSea:(DECK_Y-seaLevel)*S});
  // An open view corridor: only a low roofed link, not a tall structure.
  floor(0,1,2.2,26.5,2);
  box([30.5,2.55,2],[9,.13,2.4],edge);
  for(const x of [28,31,34])for(const z of [.9,3.1])box([x,1.3,z],[.09,2.6,.09],steel);
  const cx=(HALL.west+HALL.east)/2,cz=0;
  room('Low sea-facing seminar hall',cx,cz,HALL.east-HALL.west,HALL.south-HALL.north,HALL.clearHeight,0,['west','south'],false,false);
  const carpetMaterial=new THREE.MeshStandardMaterial({color:'#9d8d79',roughness:1,metalness:0,envMapIntensity:.08,normalMap:pale.normalMap,normalScale:new THREE.Vector2(.12,.12),roughnessMap:pale.roughnessMap});
  const tierCarpets=['#7d6e5c','#8e7e6a'].map(color=>{const material=carpetMaterial.clone();material.color.set(color);return material;});
  const carpet=new THREE.Mesh(new THREE.BoxGeometry(HALL.east-HALL.west-.16,.024,HALL.south-HALL.north-.16),carpetMaterial);
  carpet.name='Warm woven seminar carpet';carpet.position.set(cx,DECK_Y+.016,0);carpet.receiveShadow=true;scene.add(carpet);
  // Four thin roof leaves telescope onto two side cassettes. A fixed warm
  // light cove remains at the perimeter; nothing spans the open central sky.
  const roof=new THREE.Group();roof.name='Retractable seminar sky roof';scene.add(roof);
  const hallDepth=HALL.south-HALL.north,panelDepth=hallDepth/4;
  const leaves=[],roofY=DECK_Y+HALL.clearHeight/S+.12;
  for(const x of [HALL.west-.12,HALL.east+.12])box([x,roofY,0],[.28,.28,hallDepth+.5],shell);
  for(const sign of [-1,1]){
    box([cx,roofY,sign*(hallDepth/2+.25)],[9.05,.3,.52],shell);
    box([cx,roofY-.13,sign*(hallDepth/2-.04)],[8.25,.035,.09],light);
    for(let i=0;i<2;i++){
      const leaf=new THREE.Group();roof.add(leaf);leaves.push({leaf,sign,i});
      const panel=new THREE.Mesh(new THREE.BoxGeometry(8.75,.13,panelDepth),shell);panel.castShadow=true;panel.receiveShadow=true;leaf.add(panel);
      const inset=new THREE.Mesh(new THREE.BoxGeometry(8.1,.022,panelDepth-.55),acousticCeiling);inset.position.y=-.082;inset.receiveShadow=true;leaf.add(inset);
      for(const x of [-3.9,3.9]){const led=new THREE.Mesh(new THREE.BoxGeometry(.025,.025,panelDepth-.35),light);led.position.set(x,-.10,0);leaf.add(led);}
    }
  }
  function setRoof(open){for(const {leaf,sign,i} of leaves){leaf.position.set(cx,roofY+i*.16*open,sign*((panelDepth/2+i*panelDepth)*(1-open)+(hallDepth/2+panelDepth/2+.2)*open));}roof.userData.open=open;}
  setRoof(0);
  for(const sign of [-1,1])lightingZones.push({name:'Seminar downlight '+sign,position:[0,-.4,0],fixture:leaves.find(p=>p.sign===sign&&p.i===0).leaf,target:[39,DECK_Y,sign*2.5],gain:.8,color:'#ffe1bb'});
  meta('Seminar hall light fixtures',{type:'retractable acoustic ceiling with recessed linear diffusers',glareControlled:true});
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
  const lectern=meta('Small seminar lectern',{heightAboveFloor:1.08});
  lectern.position.set(41.3,DECK_Y,6.5);
  box([41.3,DECK_Y+.5/S,6.5],[.42/S,1/S,.42/S],steel);
  soft([41.3,DECK_Y+1.05/S,6.5],[.7/S,.08/S,.6/S],timber);
  // Operable blackout layer, separate from glazing and opaque chalkboards.
  const blind=new THREE.Mesh(new THREE.BoxGeometry(.055,HALL.clearHeight/S,hallDepth-.6),new THREE.MeshStandardMaterial({color:'#293530',roughness:1}));
  blind.name='East teaching blackout shade';blind.position.set(43.04,DECK_Y+HALL.clearHeight/(2*S),0);blind.visible=false;scene.add(blind);
  box([43.04,DECK_Y+HALL.clearHeight/S-.04,0],[.18,.12,hallDepth-.6],steel);
  // Resort chaise: teak slats, floating upholstered seat, inclined back,
  // small pillow, stitched edge, and low brushed-metal feet. All face sunrise.
  const loungers=[];
  function chaise(x,z){
    const p=(a,b,c)=>[x+a/S,DECK_Y+b/S,z+c/S],size=s=>s.map(v=>v/S);
    soft(p(0,.32,0),size([2.15,.12,.84]),timber);
    for(let i=0;i<14;i++)box(p(-.98+i*.15,.39,0),size([.085,.035,.78]),timber);
    soft(p(.36,.46,0),size([1.38,.16,.76]),darkFabric);
    soft(p(-.62,.74,0),size([.88,.16,.76]),darkFabric,[0,0,-.48]);
    soft(p(-.88,1.02,0),size([.24,.15,.65]),darkFabric,[0,0,-.48]);
    for(const a of [-.8,.8])for(const c of [-.32,.32])box(p(a,.16,c),size([.055,.32,.055]),steel);
    for(const c of [-.35,.35])box(p(.36,.547,c),size([1.24,.006,.008]),darkFabric);
    loungers.push([x,z]);
  }
  for(const z of [-16,-10,-4,4,10,16]){chaise(78,z);table(77.4,DECK_Y,z+1,.65,.65);}
  for(const z of [-23,23])for(const x of [48,60,72])chaise(x,z);
  meta('Sea terrace chaise lounges',{count:loungers.length,positions:loungers,facing:[1,0,0]});
  for(const z of [-13,13]){sofa(60,DECK_Y,z,Math.PI/2);table(61.2,DECK_Y,z,1,.7);}
  // Broad, shallow sea-access steps. Their foot lands just above mean sea
  // level; the fascia continues below it so no support piles are exposed.
  for(const [index,entry] of SEA_STEPS.entries()){
    const {x,z,dx,dz,width}=entry,n=7,tread=.38,low=seaLevel+.025;
    const rise=(DECK_Y-low)/n,heights=[];
    for(let i=0;i<n;i++){
      const top=DECK_Y-(i+1)*rise,base=seaLevel-.18,t=(i+.5)*tread;
      box([x+dx*t,(top+base)/2,z+dz*t],dx?[tread+.002,top-base,width]:[width,top-base,tread+.002],pavingMaterials[i%3]);
      heights.push(top);
    }
    // A restrained handrail only alongside the stair, not around the terrace.
    for(const sign of [-1,1]){
      const ox=-dz*sign*(width/2-.06),oz=dx*sign*(width/2-.06);
      beam([x+ox,DECK_Y+.9/S,z+oz],[x+dx*(n-.5)*tread+ox,low+.9/S,z+dz*(n-.5)*tread+oz],.018/S,brass);
      for(const i of [0,n-1]){
        const t=(i+.5)*tread,top=heights[i];
        beam([x+dx*t+ox,top,z+dz*t+oz],[x+dx*t+ox,top+.9/S,z+dz*t+oz],.016/S,brass);
      }
    }
    meta('Sea access stair '+(index+1),{...entry,steps:n,heights,riserMetres:rise*S,treadMetres:tread*S,seaLevel});
  }
  return {blind,seating,roof,setRoof,lightingZones,
    setTeachingShade(closed){blind.visible=Boolean(closed);},
    dispose(){lampRing.dispose();acousticCeiling.dispose();headrest.dispose();tierCarpets.forEach(m=>m.dispose());mineralMap.dispose();pavingMaterials.forEach(m=>m.dispose());borderMaterial.dispose();curvedShell.dispose();curvedCloth.dispose();carpet.geometry.dispose();carpetMaterial.dispose();seatCloth.dispose();shell.dispose();}
  };
}
