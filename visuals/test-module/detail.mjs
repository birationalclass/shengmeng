import * as T from '../3d/vendor/three.module.js';
// Repeated joinery and masonry are instanced per assembly, preserving its motion.
export function refineArchitecture(a){
 const batches=new Map(),box=new T.BoxGeometry(1,1,1),cyl=new T.CylinderGeometry(1,1,1,10),cone=new T.ConeGeometry(1,1,4),o=new T.Object3D(),M=a.materials;
 function part(p,geo,mat,pos,size,rot=[0,0,0]){let b=batches.get(p);if(!b)batches.set(p,b=new Map());const key=geo.uuid+mat.uuid;if(!b.has(key))b.set(key,{geo,mat,transforms:[]});o.position.set(...pos);o.scale.set(...size);o.rotation.set(...rot);o.updateMatrix();b.get(key).transforms.push(o.matrix.clone());}
 const block=(p,s,pos,m=M.stone,r)=>part(p,box,m,pos,s,r);
 function rod(p,start,end,r=.03,m=M.brass){const A=new T.Vector3(...start),B=new T.Vector3(...end),d=B.clone().sub(A);o.position.copy(A.add(B).multiplyScalar(.5));o.scale.set(r,d.length(),r);o.quaternion.setFromUnitVectors(new T.Vector3(0,1,0),d.normalize());let b=batches.get(p);if(!b)batches.set(p,b=new Map());const key=cyl.uuid+m.uuid;if(!b.has(key))b.set(key,{geo:cyl,mat:m,transforms:[]});b.get(key).transforms.push(o.matrix.clone().compose(o.position,o.quaternion,o.scale));}
 function window(p,x,y,z,w=.28,h=.55){block(p,[w+.12,h+.13,.085],[x,y,z],M.paper);block(p,[w,h,.035],[x,y,z+.06],M.dark);block(p,[.035,h,.035],[x,y,z+.09],M.brass);block(p,[w,.035,.035],[x,y,z+.09],M.brass);block(p,[w+.18,.07,.15],[x,y-h/2-.08,z+.02],M.stone);}
 function house(p,x,z,s=1,chinese=false){const g=new T.Group();g.position.set(x,.20,z);g.scale.setScalar(s);g.rotation.y=Math.atan2(x,z)+Math.PI;p.add(g);block(g,[1.16,.13,1.1],[0,.065,0],M.stone);block(g,[1,.94,.86],[0,.6,0],chinese?M.paper:M.stone);for(const sign of [-1,1])block(g,[.72,.075,1.08],[sign*.29,1.24,0],M.dark,[0,0,-sign*.59]);rod(g,[0,1.43,-.57],[0,1.43,.57],.04);window(g,-.25,.73,.46,.22,.36);block(g,[.26,.57,.06],[.24,.44,.47],M.wood);for(const sign of [-1,1])block(g,[.065,1.0,.09],[sign*.46,.6,.47],M.wood);block(g,[1,.065,.09],[0,.96,.47],M.wood);if(!chinese)block(g,[.16,.45,.19],[.28,1.43,-.24],M.stone);for(let j=-3;j<=3;j++)for(const sign of [-1,1])rod(g,[sign*.02,1.45,j*.14],[sign*.60,1.06,j*.14],.012,M.brass);return g;}
 // Small quarters at the rear and sides give each landmark an inhabited scale.
 a.platforms.forEach((p,i)=>{const town=new T.Group();p.add(town);a.risers.push({object:town,start:[13,42,72,102,132,163][i],end:[21,51,80,111,141,172][i]});
  if(i<4)for(let j=0;j<30;j++){const angle=1.55+j*3.18/29,r=4.85+(j%3)*.47;house(town,Math.sin(angle)*r,Math.cos(angle)*r,.49+(j%3)*.065,i===1);}
  // Machined base: ring of recessed metal ribs and two staggered rows of fasteners.
  for(let k=0;k<64;k++){const q=k*Math.PI/32;block(p,[.13,.35,.13],[7.42*Math.sin(q),-.5,7.42*Math.cos(q)],M.brass,[0,q,0]);if(k%2===0)part(p,cyl,M.gold,[7.30*Math.sin(q),-.14,7.30*Math.cos(q)],[.045,.065,.045]);}
 });
 // Curved courtyard roof battens and pavilion rafters show construction at close range.
 if(a.chineseHall){const h=a.chineseHall;for(let j=-13;j<=13;j++)for(const sign of [-1,1])rod(h,[j*.135,2.13,0],[j*.135,1.78,sign*1.14],.026,M.jade);for(const x of [-1.2,1.2])for(let k=0;k<3;k++)block(h,[.3+k*.1,.055,.32],[x,1.56+k*.08,1.16],M.wood);}
 if(a.pavilion){const p=a.pavilion;for(let j=0;j<12;j++){const q=j*Math.PI/6;rod(p,[0,2.58,0],[Math.sin(q)*1.46,1.90,Math.cos(q)*1.46],.027,M.jade);}for(let j=0;j<6;j++){const q=j*Math.PI/3,r=q+Math.PI/3;rod(p,[Math.sin(q)*.91,1.82,Math.cos(q)*.91],[Math.sin(r)*.91,1.82,Math.cos(r)*.91],.045,M.wood);}}
 const church=a.cathedral;
 if(church){
  // Cornices and individually articulated stone courses; projecting jambs stay off wall faces.
  for(let y=.35;y<2.6;y+=.39){for(const sign of [-1,1])block(church,[.075,.045,4.35],[sign*1.78,y,-.6]);}
  for(const sign of [-1,1]){
   for(const y of [.24,1.52,2.9,4.50])block(church,[1.28,.10,1.24],[sign*1.62,y,1.48],M.paper);
   for(const dx of [-.52,.52])for(const dz of [-.52,.52])block(church,[.11,4.66,.11],[sign*1.62+dx,2.35,1.48+dz],M.paper);
   for(let j=0;j<5;j++){const z=-2.4+j*.81;// side window assembled in a rotated local frame
    const w=new T.Group();church.add(w);w.position.set(sign*1.805,0,z);w.rotation.y=sign*Math.PI/2;window(w,0,1.92,0,.36,.91);
    for(let n=0;n<8;n++){const u=n/7;block(church,[.18,.16,.25],[sign*(2.11-u*.5),1.7+u*.94,z],M.paper);}
   }
  }
  for(const x of [-1.12,1.12])block(church,[.11,3.6,.18],[x,1.8,2.11],M.paper);
  for(const y of [.16,1.83,3.43])block(church,[2.46,.1,.23],[0,y,2.1],M.paper);
  for(const x of [-.7,0,.7])for(let layer=0;layer<3;layer++){const r=.28+layer*.058;for(let k=0;k<12;k++){const q=Math.PI*k/11;block(church,[.074,.13,.075],[x+Math.cos(q)*r,1.22+Math.sin(q)*r*1.75,2.17+layer*.032],M.paper,[0,0,q-Math.PI/2]);}}
  for(let k=0;k<24;k++){const q=k*Math.PI/12;part(church,cyl,M.paper,[Math.cos(q)*.56,2.62+Math.sin(q)*.56,2.16],[.027,.13,.027],[Math.PI/2,0,0]);}
  for(let j=0;j<9;j++){const z=-2.78+j*.54;for(const sign of [-1,1])rod(church,[0,3.88,z],[sign*1.64,2.73,z],.026,M.brass);}
  // A slender crossing fleche and side chapels complete the silhouette.
  part(church,cyl,M.stone,[0,3.8,-.55],[.32,.9,.32]);part(church,cone,M.dark,[0,4.77,-.55],[.47,1.1,.47],[0,Math.PI/4,0]);rod(church,[0,5.25,-.55],[0,5.7,-.55],.027,M.gold);rod(church,[-.12,5.55,-.55],[.12,5.55,-.55],.025,M.gold);
  for(const sign of [-1,1])for(let j=0;j<3;j++){const chapel=new T.Group();church.add(chapel);chapel.position.set(sign*1.96,0,-1.8+j*1.18);chapel.rotation.y=sign*Math.PI/2;block(chapel,[.8,1.3,.9],[0,.64,0]);part(chapel,cone,M.dark,[0,1.6,0],[.65,.65,.72],[0,Math.PI/4,0]);window(chapel,0,.8,.47,.32,.6);}
  for(let j=0;j<7;j++)block(church,[3.5-j*.12,.13, .36],[0,-.12-j*.08,2.30+j*.30],M.stone);
 }
 // Pagoda: structural bracket clusters, latticed screens and visibly raised tile ribs.
 for(const [i,f]of a.pagodaFloors.entries()){const w=3.5-i*.49;
  for(let side=0;side<4;side++){const g=new T.Group();f.level.add(g);g.rotation.y=side*Math.PI/2;
   for(let j=-2;j<=2;j++){const x=j*w*.34;for(let k=0;k<3;k++){block(g,[.22+k*.12,.075,.34+k*.10],[x,1.03+k*.105,w*.78],M.wood);block(g,[.08,.12,.28],[x,1.06+k*.105,w*.79],M.brass);}if(Math.abs(j)<2){block(g,[w*.28,.67,.07],[x,.62,w*.53],M.wood);for(let n=-2;n<=2;n++)block(g,[.025,.6,.028],[x+n*w*.044,.64,w*.58],M.gold);for(let n=0;n<3;n++)block(g,[w*.26,.025,.028],[x,.44+n*.18,w*.59],M.brass);}}
  }
  for(let side=0;side<4;side++){const rot=side*Math.PI/2;for(let j=-8;j<=8;j++){const q=j/8;for(let k=0;k<6;k++){const points=[k/6,(k+1)/6].map(u=>{const e=w*1.12*(1-u*.74),x=q*e,z=e;return [x*Math.cos(rot)-z*Math.sin(rot),1.265+.53*u*u+.16*(1-u)**5+.09*Math.abs(q)**6*(1-u),x*Math.sin(rot)+z*Math.cos(rot)];});rod(f.roofRoot,points[0],points[1],.024,M.jade);}}}
 }
 // Newton's manor is a complete small Tudor building with leaded windows and timber framing.
 if(a.manor){const h=a.manor;for(const x of [-.87,0,.87])block(h,[.085,1.47,.09],[x,.76,.77],M.wood);for(const y of [.18,.81,1.45])block(h,[2.02,.06,.09],[0,y,.77],M.wood);for(const x of [-.62,0,.62])for(const y of [.5,1.1])window(h,x,y,.80,.22,.32);for(const side of [-1,1])for(let j=0;j<4;j++)rod(h,[side*.09,1.63,-.6+j*.35],[side*.95,1.63,-.6+j*.35],.025,M.brass);block(h,[2.2,.13,.4],[0,-.07,1.01],M.stone);}
 // Letter archive colonnade: bases, capitals, scroll cabinets, and carved paneling.
 for(const x of [-4.4,4.4])for(let j=0;j<7;j++){const z=-3.6+j*1.12;part(a.writing,cyl,M.paper,[x,1.16,z],[.13,1.75,.13]);block(a.writing,[.45,.12,.44],[x,.32,z]);block(a.writing,[.40,.11,.40],[x,2.04,z],M.paper);block(a.writing,[.33,.09,.30],[x,1.91,z],M.brass);}for(const x of [-4.4,4.4])block(a.writing,[.32,.18,7.5],[x,2.21,-.2],M.stone);
 // Exhibition hall: repeating trusses, cross-bracing, and riveted column feet.
 for(let j=0;j<9;j++){const z=-3.4+j*.85;for(const sign of [-1,1]){rod(a.crystal,[sign*3.7,.5,z],[sign*3.7,3.6,z],.043,M.brass);for(let k=0;k<8;k++){const q=k*Math.PI/16,q2=(k+1)*Math.PI/16;rod(a.crystal,[sign*Math.cos(q)*3.7,3.6+Math.sin(q)*3.2,z],[sign*Math.cos(q2)*3.7,3.6+Math.sin(q2)*3.2,z],.042,M.dark);}if(j<8){rod(a.crystal,[sign*3.7,.6,z],[sign*3.7,3.5,z+.85],.023,M.brass);rod(a.crystal,[sign*3.7,3.5,z],[sign*3.7,.6,z+.85],.023,M.brass);}}}
 // AI towers retain a mechanical language: vertical fins, heatsinks and cable galleries.
 for(let j=0;j<12;j++){const q=j*Math.PI/6,x=Math.sin(q)*5.35,z=Math.cos(q)*5.35;for(let k=-2;k<=2;k++)block(a.ai,[.027,1.1,.65],[x+k*.095,.83,z],M.brass);}
 // Bridge bolts, diagonal timber braces and hinge barrels.
 for(const b of a.bridges)for(const pivot of b.leaves){for(const x of [-1.1,1.1]){for(let j=0;j<=8;j++)part(pivot,cyl,M.gold,[x,.097,b.length*j/16],[.04,.04,.04]);rod(pivot,[x,.16,0],[x,.78,b.length/8],.033,M.wood);rod(pivot,[x,.78,b.length*3/8],[x,.16,b.length/2],.033,M.wood);}part(pivot,cyl,M.brass,[0,0,0],[.16,2.65,.16],[0,0,Math.PI/2]);}
 const anchors=new Set([...a.platforms,...a.risers.map(r=>r.object),...a.pagodaFloors.flatMap(f=>[f.level,f.roofRoot]),...a.bridges.flatMap(b=>b.leaves)]),merged=new Map();
 for(const [parent,b]of batches){let root=parent;const relative=new T.Matrix4();while(root.parent&&!anchors.has(root)){root.updateMatrix();relative.premultiply(root.matrix);root=root.parent;}let dest=merged.get(root);if(!dest)merged.set(root,dest=new Map());for(const [key,{geo,mat,transforms}]of b){if(!dest.has(key))dest.set(key,{geo,mat,transforms:[]});dest.get(key).transforms.push(...transforms.map(m=>relative.clone().multiply(m)));}}
 for(const [parent,b]of merged)for(const {geo,mat,transforms}of b.values()){const mesh=new T.InstancedMesh(geo,mat,transforms.length);transforms.forEach((matrix,i)=>mesh.setMatrixAt(i,matrix));mesh.castShadow=true;mesh.receiveShadow=false;mesh.computeBoundingSphere();parent.add(mesh);}
}
