import * as THREE from 'three';
import {BUILDING_SCALE as S,DECK_Y,HALL,POOL_LEVEL,POOL_DEPTH,poolTopology,BRIDGES,bridgeHeight,SUNRISE_EDGE,GARDEN_PADS,GIANT_TREES,ORNAMENTAL_TREES} from './site-layout.js?v=11-open-sea';

// Architectural geometry for the approved layout. Pool surfaces are a union,
// classrooms are dry, and the offshore structure never becomes new terrain.
export function createCampus(scene,{box,soft,beam,floor,glazing,railing,sofa,table,planter,instance,cylinder,materials,Water,waterNormal}){
  const {steel,stone,edge,brass,timber,pale,darkFabric,soil,glass,light,blackboard}=materials;
  const shell=new THREE.MeshStandardMaterial({color:'#e4d5bd',roughness:.48,metalness:.08});
  const seatCloth=new THREE.MeshStandardMaterial({color:'#aa9076',roughness:.97,normalMap:pale.normalMap,roughnessMap:pale.roughnessMap});
  const poolTile=new THREE.MeshStandardMaterial({color:'#124d53',roughness:.35,metalness:.08});
  const meta=(name,data)=>{const o=new THREE.Object3D();o.name=name;o.userData=data;scene.add(o);return o;};
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
    box([cx,y+h-.13,cz],[w-.5,.024,.034],light);}
    meta(name,{bounds:[cx-w/2,cx+w/2,cz-d/2,cz+d/2],floorY:y,clearHeight:clear,dry:true});
    return roof;
  }
  function archBridge(b,i){
    const n=24;
    for(let k=0;k<n;k++){
      const a=k/n,c=(k+1)/n,ya=bridgeHeight(b,a),yc=bridgeHeight(b,c),x=b.x+(a+c-1)*b.span/2;
      box([x,(ya+yc)/2-.045,b.z],[b.span/n+.013,.09,b.width],timber,[0,0,Math.atan2(yc-ya,b.span/n)]);
      for(const sign of [-1,1])beam([b.x+(a-.5)*b.span,ya+1/S,b.z+sign*b.width/2],[b.x+(c-.5)*b.span,yc+1/S,b.z+sign*b.width/2],.022,steel);
    }
    for(let k=0;k<=6;k++)for(const sign of [-1,1]){
      const t=k/6,x=b.x+(t-.5)*b.span,y=bridgeHeight(b,t);
      beam([x,y,b.z+sign*b.width/2],[x,y+1/S,b.z+sign*b.width/2],.025,steel);
    }
    meta('Small arch bridge '+(i+1),{...b,deckY:DECK_Y,ends:[b.x-b.span/2,b.x+b.span/2],steps:false});
    // A separate level companion deck lets the water court remain reachable
    // without climbing the curved bridge. This is not accessibility certification.
    const z=b.z+b.width/2+1.0;
    floor(0,b.span,1.2,b.x,z);railing(b.x,DECK_Y,z+.6,b.span);
    meta('Level pool crossing '+(i+1),{x:b.x,z,width:1.2,span:b.span,deckY:DECK_Y});
  }
  // Main house: two dry, modest wings flank the open-to-sky water court.
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
  // Exterior stair runs beside the west wing, clear of the water branches.
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
  // Dry entry paths avoid swimming lanes except at the three modeled crossings.
  floor(0,47,2.6,-46.5,8);floor(0,2.6,23,-46,-4.8);floor(0,2.5,2.6,-44.75,-16);
  floor(0,2.6,48,-63,-16);floor(0,3,2.6,-61.5,-28);floor(0,12,2.6,-57,-38);
  floor(0,38,2.2,-43,24.5);floor(0,2.2,19,-24,17);
  // Modular offshore garden trays and service spines; seawater stays beneath.
  for(const [a,b,c,d] of GARDEN_PADS){
    box([(a+b)/2,-.2,(c+d)/2],[b-a,.5,d-c],edge);
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

  // A supported offshore platform: ocean remains under the hall, not landfill.
  floor(0,26,21,40,0);
  meta('Expanded sea lounge terrace',{bounds:[27,53,-10.5,10.5],eastClearance:53-HALL.east,poolRailings:false});
  // An open view corridor: only a low roofed link, not a tall structure.
  floor(0,1,2.2,26.5,2);
  box([30.5,2.55,2],[9,.13,2.4],edge);
  for(const x of [28,31,34])for(const z of [.9,3.1])box([x,1.3,z],[.09,2.6,.09],steel);
  const cx=(HALL.west+HALL.east)/2,cz=0;
  room('Low sea-facing seminar hall',cx,cz,HALL.east-HALL.west,HALL.south-HALL.north,HALL.clearHeight,0,['west','south'],false,false);
  // Four thin roof leaves telescope onto two side cassettes. A fixed warm
  // light cove remains at the perimeter; nothing spans the open central sky.
  const roof=new THREE.Group();roof.name='Retractable seminar sky roof';scene.add(roof);
  const leaves=[],roofY=DECK_Y+HALL.clearHeight/S+.12;
  for(const x of [HALL.west-.12,HALL.east+.12])box([x,roofY,0],[.28,.28,8.9],shell);
  for(const sign of [-1,1]){
    box([cx,roofY,sign*4.45],[9.05,.3,.52],shell);
    box([cx,roofY-.13,sign*4.16],[8.25,.035,.09],light);
    for(let i=0;i<2;i++){
      const leaf=new THREE.Group();roof.add(leaf);leaves.push({leaf,sign,i});
      const panel=new THREE.Mesh(new THREE.BoxGeometry(8.75,.13,2.1),shell);panel.castShadow=true;panel.receiveShadow=true;leaf.add(panel);
      const inset=new THREE.Mesh(new THREE.BoxGeometry(8.1,.022,1.55),timber);inset.position.y=-.082;leaf.add(inset);
      for(const x of [-3.9,3.9]){const led=new THREE.Mesh(new THREE.BoxGeometry(.025,.025,1.75),light);led.position.set(x,-.10,0);leaf.add(led);}
    }
  }
  function setRoof(open){for(const {leaf,sign,i} of leaves){leaf.position.set(cx,roofY+i*.16*open,sign*((1.05+i*2.1)*(1-open)+5.4*open));}roof.userData.open=open;}
  setRoof(0);
  // Opaque north acoustic strip, not the writing wall: the boards face WEST
  // from the east glazing and listeners face EAST toward the sunrise.
  box([cx,DECK_Y+1.05,HALL.north+.09],[HALL.east-HALL.west-.3,2.1,.12],timber);
  const seating=meta('Mathematics auditorium seating',{seats:32,rows:4,centralAisle:1.6,facing:[1,0,0],seatPositions:[],clearHeight:HALL.clearHeight,offshore:true});
  function chair(x,z,index){
    const angle=Math.PI/2;
    const pos=p=>new THREE.Vector3(...p).divideScalar(S).applyAxisAngle(new THREE.Vector3(0,1,0),angle).add(new THREE.Vector3(x,DECK_Y,z)).toArray();
    const part=(p,size,m,round=false)=>(round?soft:box)(pos(p),size.map(v=>v/S),m,[0,angle,0]);
    part([0,.025,0],[.48,.045,.62],brass);
    beam(pos([0,.055,.1]),pos([0,.46,-.16]),.035/S,brass);
    part([0,.48,.0],[.7,.095,.7],shell,true);part([0,.55,.02],[.64,.16,.62],seatCloth,true);
    part([0,.94,-.31],[.7,.76,.12],shell,true);part([0,.95,-.22],[.61,.63,.14],seatCloth,true);
    part([0,1.2,-.17],[.48,.15,.11],pale,true);
    for(const sign of [-1,1]){part([sign*.355,.71,0],[.055,.065,.54],brass);part([sign*.355,.76,.0],[.1,.085,.43],seatCloth,true);}
    // A few deployed writing tablets show their function without blocking every aisle.
    part([.4,.73,index%4===0?.26:-.07],index%4===0?[.48,.04,.32]:[.035,.30,.32],timber,true);
  }
  for(let row=0;row<4;row++)for(const [i,z] of [-3.15,-2.35,-1.55,-.75,.75,1.55,2.35,3.15].entries()){
    const x=35.9+row*1.1;chair(x,z,row*8+i);seating.userData.seatPositions.push([x,DECK_Y,z]);
  }
  const lectern=meta('Small seminar lectern',{heightAboveFloor:1.08});
  lectern.position.set(41.3,DECK_Y,3.2);
  box([41.3,DECK_Y+.5/S,3.2],[.42/S,1/S,.42/S],steel);
  soft([41.3,DECK_Y+1.05/S,3.2],[.7/S,.08/S,.6/S],timber);
  // Operable blackout layer, separate from glazing and opaque chalkboards.
  const blind=new THREE.Mesh(new THREE.BoxGeometry(.055,HALL.clearHeight/S,7.8),new THREE.MeshStandardMaterial({color:'#293530',roughness:1}));
  blind.name='East teaching blackout shade';blind.position.set(43.04,DECK_Y+HALL.clearHeight/(2*S),0);blind.visible=false;scene.add(blind);
  box([43.04,DECK_Y+HALL.clearHeight/S-.04,0],[.18,.12,7.8],steel);
  // Resort chaise: teak slats, floating upholstered seat, inclined back,
  // small pillow, stitched edge, and low brushed-metal feet. All face sunrise.
  const loungers=[];
  function chaise(x,z){
    const p=(a,b,c)=>[x+a/S,DECK_Y+b/S,z+c/S],size=s=>s.map(v=>v/S);
    soft(p(0,.32,0),size([2.15,.12,.84]),timber);
    for(let i=0;i<14;i++)box(p(-.98+i*.15,.39,0),size([.085,.035,.78]),timber);
    soft(p(.36,.46,0),size([1.38,.16,.76]),pale);
    soft(p(-.62,.74,0),size([.88,.16,.76]),pale,[0,0,-.48]);
    soft(p(-.88,1.02,0),size([.24,.15,.65]),darkFabric,[0,0,-.48]);
    for(const a of [-.8,.8])for(const c of [-.32,.32])box(p(a,.16,c),size([.055,.32,.055]),steel);
    for(const c of [-.35,.35])box(p(.36,.547,c),size([1.24,.006,.008]),darkFabric);
    loungers.push([x,z]);
  }
  for(const z of [-7.8,-5.6,-3.4,3.4,5.6,7.8]){chaise(50.1,z);table(49.5,DECK_Y,z+1,.65,.65);}
  for(const z of [-8,8])for(const x of [35.5,39.5,43.5])chaise(x,z);
  meta('Sunrise pool chaise lounges',{count:loungers.length,positions:loungers,facing:[1,0,0]});
  for(const z of [-6.5,6.5]){sofa(46,DECK_Y,z,Math.PI/2);table(47.2,DECK_Y,z,1,.7);}
  // No fence, glass wall or handrail surrounds the infinity-pool edge.
  floor(0,1.4,50,-23,0);floor(0,48,1.4,2,-25);floor(0,48,1.4,2,25);

  const topology=poolTopology(),vertices=[],uv=[];
  for(const [a,b,c,d] of topology.cells){
    // Water's reflection normal is local +Z; rotate the entire XY surface to XZ.
    for(const [x,z] of [[a,c],[a,d],[b,c],[b,c],[a,d],[b,d]]){vertices.push(x,-z,0);uv.push(x*.12,z*.12);}
    box([(a+b)/2,POOL_LEVEL-POOL_DEPTH-.075,(c+d)/2],[b-a,.15,d-c],poolTile);
  }
  for(const [a,c,b,d] of topology.edges){
    const horizontal=c===d,length=Math.hypot(b-a,d-c),cx=(a+b)/2,cz=(c+d)/2;
    const overflow=(a===SUNRISE_EDGE&&b===SUNRISE_EDGE)||(c===d&&Math.abs(c)===19&&Math.min(a,b)>=26);
    box([cx,POOL_LEVEL-POOL_DEPTH/2,cz],horizontal?[length,POOL_DEPTH,.15]:[.15,POOL_DEPTH,length],poolTile);
    box([cx,overflow?POOL_LEVEL-.025:DECK_Y-.035,cz],horizontal?[length,.07,.22]:[.22,.07,length],stone);
  }
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(vertices,3));g.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));g.computeVertexNormals();g.computeBoundingSphere();
  const water=new Water(g,{textureWidth:512,textureHeight:512,waterNormals:waterNormal,sunDirection:new THREE.Vector3(1,.2,0).normalize(),sunColor:0xffe8ca,waterColor:0x23646a,distortionScale:.7,alpha:1,fog:true});
  water.name='Connected infinity pool and core water court';water.rotation.x=-Math.PI/2;water.position.y=POOL_LEVEL;water.userData.cells=topology.cells;scene.add(water);
  // Recessed overflow sheet and recovery trough: closed pool water does not
  // mingle with the sea. Analytic shimmer shares the single pool time uniform.
  const overflowMaterial=new THREE.MeshPhysicalMaterial({color:'#72cbd0',transparent:true,opacity:.48,roughness:.18,metalness:.2,side:THREE.DoubleSide,depthWrite:false});
  const overflow=new THREE.Mesh(new THREE.PlaneGeometry(38,.4),overflowMaterial);overflow.name='East infinity overflow sheet';overflow.rotation.y=Math.PI/2;overflow.position.set(SUNRISE_EDGE+.12,POOL_LEVEL-.2,0);scene.add(overflow);
  box([SUNRISE_EDGE+.3,POOL_LEVEL-.5,0],[.65,.13,38.6],poolTile);
  for(const z of [-19,19]){
    const side=new THREE.Mesh(new THREE.PlaneGeometry(36,.4),overflowMaterial);side.position.set(44,POOL_LEVEL-.2,z+Math.sign(z)*.12);side.name='Side infinity overflow sheet';scene.add(side);
    box([44,POOL_LEVEL-.5,z+Math.sign(z)*.3],[36,.13,.65],poolTile);
  }
  meta('Sunrise infinity edge',{x:SUNRISE_EDGE,facing:[1,0,0],separateFromOcean:true,poolLevel:POOL_LEVEL,railings:false});
  BRIDGES.forEach(archBridge);
  return {water,blind,seating,roof,setRoof,poolCells:topology.cells,
    setTeachingShade(closed){blind.visible=Boolean(closed);},
    dispose(){seatCloth.dispose();shell.dispose();poolTile.dispose();g.dispose();water.material.uniforms.mirrorSampler.value.dispose();water.material.dispose();overflow.geometry.dispose();overflowMaterial.dispose();}
  };
}
