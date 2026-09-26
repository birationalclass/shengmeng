import * as T from '../3d/vendor/three.module.js';
export function createGrandPiano(){
 const root=new T.Group();root.name='Concert grand piano';
 const ebony=new T.MeshPhysicalMaterial({color:0x101518,metalness:.16,roughness:.26,clearcoat:.65,clearcoatRoughness:.16,envMapIntensity:.35});
 const ivory=new T.MeshStandardMaterial({color:0xece9df,roughness:.36}),black=new T.MeshStandardMaterial({color:0x111416,roughness:.32});
 const gold=new T.MeshStandardMaterial({color:0xa18b54,metalness:.7,roughness:.4}),spruce=new T.MeshStandardMaterial({color:0x8c663f,roughness:.8}),felt=new T.MeshStandardMaterial({color:0x642d32,roughness:1}),leather=new T.MeshStandardMaterial({color:0x242725,roughness:.8});
 const geometries=[],materials=[ebony,ivory,black,gold,spruce,felt,leather],batches=new Map(),box=new T.BoxGeometry(),cylinder=new T.CylinderGeometry(1,1,1,12),matrix=new T.Matrix4();geometries.push(box,cylinder);
 const part=(g,m,p,s,r=new T.Quaternion())=>{const key=g.uuid+m.uuid;if(!batches.has(key))batches.set(key,{g,m,items:[]});matrix.compose(new T.Vector3(...p),r,new T.Vector3(...s));batches.get(key).items.push(matrix.clone());};
 const block=(p,s,m=ebony)=>part(box,m,p,s);
 function rod(a,b,r,m){const A=new T.Vector3(...a),B=new T.Vector3(...b),d=B.clone().sub(A);part(cylinder,m,A.add(B).multiplyScalar(.5).toArray(),[r,d.length(),r],new T.Quaternion().setFromUnitVectors(new T.Vector3(0,1,0),d.normalize()));}
 const outline=new T.Shape();outline.moveTo(-.78,0);outline.lineTo(.78,0);outline.lineTo(.78,-.78);outline.bezierCurveTo(.78,-1.1,.23,-1.12,.16,-1.6);outline.bezierCurveTo(.08,-2.5,-.75,-2.67,-.78,-1.91);outline.lineTo(-.78,0);
 function panel(shape,depth,mat,y){const g=new T.ExtrudeGeometry(shape,{depth,steps:1,bevelEnabled:true,bevelSize:.014,bevelThickness:.012,bevelSegments:3,curveSegments:40});g.rotateX(Math.PI/2);geometries.push(g);const mesh=new T.Mesh(g,mat);mesh.position.y=y;mesh.castShadow=mesh.receiveShadow=true;root.add(mesh);return mesh;}
 // Shape coordinates map into the negative-Z tail after a positive quarter-turn.
 panel(outline,.15,ebony,.86);
 const soundboard=panel(outline,.018,spruce,.878);soundboard.scale.set(.94,1,.96);
 const contour=outline.getPoints(90).map(v=>new T.Vector3(v.x,.905,v.y));
 for(let i=1;i<contour.length;i++){rod(contour[i-1].toArray(),contour[i].toArray(),.025,ebony);rod([contour[i-1].x,.884,contour[i-1].z],[contour[i].x,.884,contour[i].z],.006,gold);}
 for(let i=0;i<46;i++){const x=-.66+i*.028,tail=-.72-1.28*(1-i/46);rod([x,.918,-.28],[x*.64-.12,.918,tail],.0017,gold);}
 for(const x of [-.63,-.22,.18])rod([x,.929,-.27],[x*.65-.14,.929,-1.65+Math.max(0,x)*2],.024,gold);
 block([-.10,.93,-.30],[1.24,.04,.055],gold);block([-.32,.93,-1.35],[.60,.035,.055],gold);
 // Lid hinges along the straight bass rim. Rotated around that physical edge.
 const lidPivot=new T.Group();lidPivot.position.set(-.78,.98,0);root.add(lidPivot);
 const lid=panel(outline,.038,ebony,0);root.remove(lid);lid.position.set(.78,0,0);lidPivot.add(lid);lidPivot.rotation.z=.40;
 for(const z of [-.34,-.95,-1.65])block([-.78,.971,z],[.04,.04,.12],gold);
 rod([.42,.91,-.69],[.42,1.46,-.69],.013,ebony);
 // 88 keys: 52 naturals and 36 accidentals with the correct A0–C8 grouping.
 const keyWidth=1.224/52,notes=[9,11,...Array.from({length:7},()=>[0,2,4,5,7,9,11]).flat(),0];
 block([0,.715,.14],[1.62,.095,.43]);block([0,.779,-.045],[1.27,.009,.018],felt);
 for(let i=0;i<52;i++){
  const x=-.612+(i+.5)*keyWidth;block([x,.780,.16],[keyWidth-.0011,.022,.34],ivory);
  if(i<51&&![4,11].includes(notes[i]))block([x+keyWidth/2,.809,.064],[.013,.039,.20],black);
 }
 for(const x of [-.75,.75])block([x,.81,.15],[.14,.14,.46]);
 block([0,.904,-.12],[1.42,.13,.08]);block([0,.959,-.078],[.20,.008,.007],gold);
 // Open music desk, pierced slats and a slim score ledge.
 for(const x of [-.37,.37])block([x,1.07,-.32],[.032,.30,.04]);
 for(const y of [.96,1.20])block([0,y,-.32],[.80,.035,.04]);
 for(let i=0;i<9;i++)block([-.31+i*.0775,1.08,-.32],[.018,.22,.025]);
 block([0,.969,-.265],[.84,.027,.13]);
 for(const [x,z] of [[-.64,.06],[.64,.06],[-.47,-1.82]]){
  block([x,.39,z],[.105,.66,.105]);block([x,.09,z],[.12,.08,.12],gold);
  part(cylinder,black,[x,.055,z],[.045,.085,.045],new T.Quaternion().setFromAxisAngle(new T.Vector3(1,0,0),Math.PI/2));
 }
 for(const x of [-.13,.13])rod([x,.71,-.04],[x,.19,.02],.017,ebony);
 block([0,.17,.045],[.42,.06,.14]);for(const x of [-.10,0,.10]){rod([x,.19,.02],[x,.10,.28],.009,gold);block([x,.09,.28],[.055,.024,.12],gold);}
 // Adjustable concert bench, stitched cushion and discreet brass hardware.
 block([0,.43,.91],[.82,.10,.40]);block([0,.495,.91],[.80,.07,.39],leather);
 for(const x of [-.34,.34])for(const z of [.77,1.05])block([x,.22,z],[.06,.40,.06]);
 for(const x of [-.19,0,.19])for(const z of [.83,.99])part(cylinder,black,[x,.533,z],[.010,.004,.010]);
 for(const x of [-.44,.44])part(cylinder,gold,[x,.44,.91],[.034,.025,.034],new T.Quaternion().setFromAxisAngle(new T.Vector3(0,0,1),Math.PI/2));
 for(const {g,m,items} of batches.values()){const mesh=new T.InstancedMesh(g,m,items.length);items.forEach((v,i)=>mesh.setMatrixAt(i,v));mesh.castShadow=mesh.receiveShadow=true;mesh.computeBoundingSphere();root.add(mesh);}
 root.userData={keys:88,whiteKeys:52,blackKeys:36,pedals:3,length:2.75,width:1.6,lidOpen:true};
 return {root,dispose(){geometries.forEach(g=>g.dispose());materials.forEach(m=>m.dispose());}};
}
