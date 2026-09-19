import * as THREE from 'three';
import {BUILDING_SCALE as S,DECK_Y,HALL,POOL_LEVEL,POOL_DEPTH,poolTopology,BRIDGES,bridgeHeight} from './site-layout.js?v=9-peninsula';

// Architectural geometry for the approved layout. Pool surfaces are a union,
// classrooms are dry, and the offshore structure never becomes new terrain.
export function createCampus(scene,{box,soft,beam,floor,glazing,railing,sofa,table,planter,instance,cylinder,materials,Water,waterNormal}){
  const {steel,stone,edge,brass,timber,pale,darkFabric,glass,light,blackboard}=materials;
  const shell=new THREE.MeshStandardMaterial({color:'#d4dedb',roughness:.38,metalness:.16});
  const poolTile=new THREE.MeshStandardMaterial({color:'#124d53',roughness:.35,metalness:.08});
  const meta=(name,data)=>{const o=new THREE.Object3D();o.name=name;o.userData=data;scene.add(o);return o;};
  function books(cx,y,z,w){
    box([cx,y+1.08,z],[w,2.16,.32],timber);
    for(let row=0;row<4;row++){
      box([cx,y+.12+row*.52,z+.12],[w,.045,.38],brass);
      for(let i=0;i<Math.floor(w/.19);i++)box([cx-w/2+.14+i*.19,y+.32+row*.52,z+.13],[.12,.26+(i%3)*.06,.25],i%3?blackboard:pale);
    }
  }
  function room(name,cx,cz,w,d,clear=3.2,base=0,doors=['south'],ownFloor=true){
    const y=base+DECK_Y,h=clear/S,roof=base+DECK_Y+h+.20;
    if(ownFloor)floor(base,w,d,cx,cz);floor(roof,w+.55,d+.55,cx,cz);
    for(const [side,x,z,width,axis] of [['south',cx,cz+d/2,w,'x'],['north',cx,cz-d/2,w,'x'],['west',cx-w/2,cz,d,'z'],['east',cx+w/2,cz,d,'z']]){
      if(doors.includes(side)){
        const gap=1.45,pane=(width-gap)/2;
        for(const sign of [-1,1])glazing(x+(axis==='x'?sign*(gap+pane)/2:0),y,z+(axis==='z'?sign*(gap+pane)/2:0),pane,h,axis);
      }else glazing(x,y,z,width,h,axis);
    }
    for(let x=cx-w/2+.35;x<cx+w/2;x+=.65)box([x,y+h-.08,cz],[.09,.10,d-.1],timber);
    box([cx,y+h-.13,cz],[w-.5,.024,.034],light);
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
  floor(0,51,2.6,-44.5,8);floor(0,2.6,23,-46,-4.8);floor(0,2.5,2.6,-44.75,-16);
  floor(0,2.6,48,-63,-16);floor(0,3,2.6,-61.5,-28);floor(0,12,2.6,-57,-38);
  floor(0,26,2.2,-49,23);floor(0,2.2,15,-20,16);
  // One small classical garden accent, not the dominant architectural language.
  floor(0,5,5,-35,-29);
  for(const x of [-37,-33])for(const z of [-31,-27])box([x,1.2,z],[.13,2.4,.13],timber);
  for(let i=0;i<8;i++){const w=5.9-i*.63;box([-35,2.5+i*.16,-29],[w,.12,w],edge);}
  table(-35,DECK_Y,-29,1.3,1.3);meta('Bamboo tea pavilion',{x:-35,z:-29});

  // A supported offshore platform: ocean remains under the hall, not landfill.
  floor(0,22,13,34,0);
  for(const x of [25,32,40,47])for(const z of [-5.8,5.8]){
    box([x,-2.7,z],[.45,5.4,.45],steel);
    beam([x,-1.8,z],[x+1.8,-.25,z],.065,steel);
  }
  // An open view corridor: only a low roofed link, not a tall structure.
  floor(0,1,2.2,22.5,2);
  box([28.5,2.55,2],[13,.13,2.4],edge);
  for(const x of [24,31,34])for(const z of [.9,3.1])box([x,1.3,z],[.09,2.6,.09],steel);
  const cx=(HALL.west+HALL.east)/2,cz=0;
  room('Low sea-facing seminar hall',cx,cz,HALL.east-HALL.west,HALL.south-HALL.north,HALL.clearHeight,0,['west','south'],false);
  // Opaque north acoustic strip, not the writing wall: the boards face WEST
  // from the east glazing and listeners face EAST toward the sunrise.
  box([cx,DECK_Y+1.05,HALL.north+.09],[HALL.east-HALL.west-.3,2.1,.12],timber);
  const seating=meta('Mathematics auditorium seating',{seats:32,rows:4,centralAisle:1.6,facing:[1,0,0],seatPositions:[],clearHeight:HALL.clearHeight,offshore:true});
  function chair(x,z,index){
    const angle=Math.PI/2;
    const pos=p=>new THREE.Vector3(...p).divideScalar(S).applyAxisAngle(new THREE.Vector3(0,1,0),angle).add(new THREE.Vector3(x,DECK_Y,z)).toArray();
    const part=(p,size,m,round=false)=>(round?soft:box)(pos(p),size.map(v=>v/S),m,[0,angle,0]);
    part([0,.025,0],[.48,.045,.62],steel);
    beam(pos([0,.055,.1]),pos([0,.46,-.16]),.035/S,steel);
    part([0,.48,.0],[.68,.075,.68],shell,true);part([0,.535,.02],[.61,.11,.59],darkFabric,true);
    part([0,.94,-.31],[.68,.73,.065],shell,true);part([0,.95,-.265],[.59,.58,.08],darkFabric,true);
    for(const sign of [-1,1]){part([sign*.355,.71,0],[.055,.065,.54],steel);part([sign*.355,.745,.0],[.075,.04,.38],darkFabric);}
    // A few deployed writing tablets show their function without blocking every aisle.
    part([.4,.73,index%4===0?.26:-.07],index%4===0?[.48,.04,.32]:[.035,.30,.32],shell,true);
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
  floor(0,.6,11,45.3,0);railing(44.5,DECK_Y,-5.5,2.2);railing(44.5,DECK_Y,5.5,2.2);
  for(const z of [-5.3,5.3]){sofa(44.5,DECK_Y,z,Math.PI/2);table(45,DECK_Y,z,1,.7);}
  // Perimeter deck and outward railing, below eye level; east overflow lip stays low.
  floor(0,1.4,42,-19,0);floor(0,34,1.4,0,-21);floor(0,34,1.4,0,21);
  floor(0,28.7,1.4,36.65,-12);floor(0,28.7,1.4,36.65,12);
  railing(36.65,DECK_Y,-12.7,28.7);railing(36.65,DECK_Y,12.7,28.7);

  const topology=poolTopology(),vertices=[],uv=[];
  for(const [a,b,c,d] of topology.cells){
    // Water's reflection normal is local +Z; rotate the entire XY surface to XZ.
    for(const [x,z] of [[a,c],[a,d],[b,c],[b,c],[a,d],[b,d]]){vertices.push(x,-z,0);uv.push(x*.12,z*.12);}
    box([(a+b)/2,POOL_LEVEL-POOL_DEPTH-.075,(c+d)/2],[b-a,.15,d-c],poolTile);
    if(a>=22)for(const x of [a+.25,b-.25])box([x,-2.45,(c+d)/2],[.25,4.3,.25],steel);
  }
  for(const [a,c,b,d] of topology.edges){
    const horizontal=c===d,length=Math.hypot(b-a,d-c),cx=(a+b)/2,cz=(c+d)/2;
    const overflow=a===50&&b===50;
    box([cx,POOL_LEVEL-POOL_DEPTH/2,cz],horizontal?[length,POOL_DEPTH,.15]:[.15,POOL_DEPTH,length],poolTile);
    box([cx,overflow?POOL_LEVEL-.025:DECK_Y-.035,cz],horizontal?[length,.07,.22]:[.22,.07,length],stone);
  }
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(vertices,3));g.setAttribute('uv',new THREE.Float32BufferAttribute(uv,2));g.computeVertexNormals();g.computeBoundingSphere();
  const water=new Water(g,{textureWidth:512,textureHeight:512,waterNormals:waterNormal,sunDirection:new THREE.Vector3(1,.2,0).normalize(),sunColor:0xffe8ca,waterColor:0x23646a,distortionScale:.7,alpha:1,fog:true});
  water.name='Connected infinity pool and core water court';water.rotation.x=-Math.PI/2;water.position.y=POOL_LEVEL;water.userData.cells=topology.cells;scene.add(water);
  // Recessed overflow sheet and recovery trough: closed pool water does not
  // mingle with the sea. Analytic shimmer shares the single pool time uniform.
  const overflowMaterial=new THREE.MeshPhysicalMaterial({color:'#72cbd0',transparent:true,opacity:.48,roughness:.18,metalness:.2,side:THREE.DoubleSide,depthWrite:false});
  const overflow=new THREE.Mesh(new THREE.PlaneGeometry(22,.4),overflowMaterial);overflow.name='East infinity overflow sheet';overflow.rotation.y=Math.PI/2;overflow.position.set(50.12,POOL_LEVEL-.2,0);scene.add(overflow);
  box([50.3,POOL_LEVEL-.5,0],[.65,.13,22.6],poolTile);
  meta('Sunrise infinity edge',{x:50,facing:[1,0,0],separateFromOcean:true,poolLevel:POOL_LEVEL});
  BRIDGES.forEach(archBridge);
  return {water,blind,seating,poolCells:topology.cells,
    setTeachingShade(closed){blind.visible=Boolean(closed);},
    dispose(){shell.dispose();poolTile.dispose();g.dispose();water.material.uniforms.mirrorSampler.value.dispose();water.material.dispose();overflow.geometry.dispose();overflowMaterial.dispose();}
  };
}
