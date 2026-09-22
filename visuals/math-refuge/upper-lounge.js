// Selected sketch A: west workstations, east conversation bays, north bar.
// Physical metres, with a continuous clear arrival aisle at the west door.
export function createUpperLounge(T){
  const group=new T.Group();group.name='Upper sea-view academic lounge A';
  const mats=[],geos=[],textures=[],batches=new Map(),dummy=new T.Object3D();
  const material=(color,roughness=.8,metalness=0)=>{const m=new T.MeshStandardMaterial({color,roughness,metalness,envMapIntensity:.18});mats.push(m);return m;};
  const oak=material('#9d7953'),wood=material('#71523b'),bronze=material('#9c815b',.6,.55),dark=material('#263334'),rubber=material('#1d2426',.95),ceramic=material('#c8bba2'),leaf=material('#396552'),soil=material('#44392c');
  const colors=['#6997b5','#8eac89','#c58e9e','#9990b9','#c3ae62','#929b9c'],paint=colors.map(c=>material(c,.58,.28));
  const cloth=['#709b87','#ba8070','#858da9'].map(c=>material(c,.98));
  const warm=material('#d4b282',.86),rug=material('#b5a68d',1),rugBlue=material('#738e8f',1);
  function geom(g){geos.push(g);return g;}
  const cube=geom(new T.BoxGeometry(1,1,1)),cyl=geom(new T.CylinderGeometry(1,1,1,24)),ball=geom(new T.SphereGeometry(1,12,8));
  function part(g,m,p,s=[1,1,1],r=[0,0,0],frame=null){
    dummy.position.fromArray(p);dummy.scale.fromArray(s);dummy.rotation.set(...r);dummy.updateMatrix();const matrix=dummy.matrix.clone();if(frame)matrix.premultiply(frame);
    const key=g.uuid+':'+m.uuid;if(!batches.has(key))batches.set(key,{g,m,matrices:[]});batches.get(key).matrices.push(matrix);
  }
  const box=(p,s,m,frame=null,r=[0,0,0])=>part(cube,m,p,s,r,frame);
  function frame(x,y,z,angle=0){return new T.Matrix4().compose(new T.Vector3(x,y,z),new T.Quaternion().setFromAxisAngle(new T.Vector3(0,1,0),angle),new T.Vector3(1,1,1));}
  function meta(name,data){const o=new T.Object3D();o.name=name;o.userData=data;group.add(o);return o;}
  function stem(a,b,r,m,f){const va=new T.Vector3(...a),vb=new T.Vector3(...b),d=vb.clone().sub(va),q=new T.Quaternion().setFromUnitVectors(new T.Vector3(0,1,0),d.clone().normalize()),e=new T.Euler().setFromQuaternion(q);part(cyl,m,va.add(vb).multiplyScalar(.5).toArray(),[r,d.length(),r],[e.x,e.y,e.z],f);}
  function plant(x,z,height=.8,y=0){
    part(cyl,bronze,[x,y+.14,z],[.16,.28,.16]);part(cyl,soil,[x,y+.283,z],[.145,.006,.145]);
    stem([x,y+.26,z],[x,y+height,z],.012,wood);
    for(let i=0;i<8;i++){const a=i*2.4,yy=y+.36+i*height*.066,dx=Math.cos(a)*.18,dz=Math.sin(a)*.18;stem([x,yy,z],[x+dx,yy+.13,z+dz],.005,wood);part(ball,leaf,[x+dx,yy+.15,z+dz],[.10,.20,.025],[.4,a,.4]);}
  }
  // Muted oak planks and inset textile islands; no shiny white floor.
  for(let i=0;i<24;i++)box([-4.692+i*.408,.012,0],[.403,.023,18.26],i%4?oak:wood);
  box([-.3,.027,1.0],[1.40,.015,12.0],rug);
  for(let i=0;i<5;i++)box([-.3,.037,-3.8+i*2.2],[1.1,.004,.13],rugBlue,null,[0,.5,0]);
  const canvas=document.createElement('canvas');canvas.width=768;canvas.height=480;
  const c=canvas.getContext('2d');c.fillStyle='#233b45';c.fillRect(0,0,768,480);c.fillStyle='#c0d4d0';c.font='22px serif';c.fillText('iMac  /  MATHEMATICS STUDIO',35,43);
  c.fillStyle='#38565e';c.fillRect(28,69,450,345);c.fillStyle='#24383f';c.fillRect(498,69,242,345);
  c.fillStyle='#e0e8d9';c.font='28px serif';for(const [i,t] of ['E₂ → E₃ → ··· → E∞','Hⁿ(X, ℂ) = ⊕ Hᵖ⸴ᑫ','∇ · v = 0','Ideas begin with a question.'].entries())c.fillText(t,50,125+i*72);
  c.font='18px sans-serif';for(let i=0;i<9;i++)c.fillText(['Research notes','Outline / Proof','References'][i%3],516,112+i*33);
  const screen=new T.CanvasTexture(canvas);screen.colorSpace=T.SRGBColorSpace;textures.push(screen);const screenMat=new T.MeshBasicMaterial({map:screen,toneMapped:false});mats.push(screenMat);
  const plane=geom(new T.PlaneGeometry(1,1));
  const stations=[];
  for(const [i,z] of [-6.6,-4.55,-2.5,2.5,4.55,6.6].entries()){
    const x=-4.07,f=frame(x,0,z,Math.PI/2),m=paint[i];stations.push({x,z,color:colors[i],width:1.4,depth:.72});
    box([0,.735,0],[1.4,.055,.72],m,f);
    for(const px of [-.60,.60])for(const pz of [-.27,.27])box([px,.36,pz],[.035,.70,.035],bronze,f);
    box([0,.965,-.18],[.085,.36,.025],m,f);box([0,.78,-.10],[.20,.018,.20],m,f);
    box([0,1.175,-.19],[.55,.405,.014],m,f);box([0,1.193,-.179],[.526,.341,.009],ceramic,f);
    part(plane,screenMat,[0,1.193,-.173],[.507,.318,1],[0,0,0],f);
    part(ball,rubber,[0,1.375,-.179],[.003,.003,.003],[0,0,0],f);
    box([-.06,.773,.16],[.37,.016,.13],ceramic,f);
    for(let row=0;row<4;row++)for(let key=0;key<12;key++)box([-.224+key*.029,.783,.115+row*.027],[.023,.003,.018],dark,f);
    part(ball,ceramic,[.31,.786,.17],[.026,.013,.048],[0,0,0],f);
    // Five-star swivel chair: curved upholstered shell and soft, low arms.
    part(ball,m,[0,.48,.91],[.29,.085,.28],[0,0,0],f);part(ball,m,[0,.78,1.12],[.29,.32,.055],[-.15,0,0],f);
    part(cyl,bronze,[0,.26,.91],[.035,.41,.035],[0,0,0],f);
    for(let j=0;j<5;j++){const a=j*Math.PI*2/5,px=Math.cos(a)*.27,pz=.91+Math.sin(a)*.27;stem([0,.09,.91],[px,.06,pz],.012,bronze,f);part(ball,rubber,[px,.045,pz],[.03,.04,.03],[0,0,0],f);}
    for(const sign of [-1,1]){stem([sign*.25,.51,.95],[sign*.25,.66,.9],.012,bronze,f);box([sign*.25,.67,.91],[.065,.035,.24],m,f);}
  }
  meta('Six color iMac workstations',{stations,entranceGapMetres:3.6});
  function sector(inner,outer,start,end,height){const s=new T.Shape();s.absarc(0,0,outer,start,end,false);s.absarc(0,0,inner,end,start,true);s.closePath();const g=new T.ExtrudeGeometry(s,{depth:height,bevelEnabled:true,bevelSegments:2,steps:1,bevelSize:.025,bevelThickness:.025,curveSegments:32});g.rotateX(-Math.PI/2);return geom(g);}
  const sofaBase=sector(1.00,1.77,-Math.PI*2/3,Math.PI*2/3,.18),sofaBack=sector(1.52,1.78,-Math.PI*2/3,Math.PI*2/3,.50);
  const cushion=sector(1.04,1.51,-Math.PI/3+.025,Math.PI/3-.025,.14);
  const discussions=[];
  for(const [i,z] of [-4.75,.45,5.6].entries()){
    const x=2.62,m=cloth[i];discussions.push({x,z,radius:1.81,opening:'west',tableRadius:.64});
    part(cyl,rug,[x,.039,z],[1.92,.018,1.92]);
    part(sofaBase,wood,[x,.15,z]);part(sofaBack,m,[x,.37,z]);
    for(const a of [-1.9,-.95,0,.95,1.9])for(const r of [1.13,1.64])part(cyl,bronze,[x+r*Math.cos(a),.087,z+r*Math.sin(a)],[.032,.15,.032]);
    for(const a of [-Math.PI/3,Math.PI/3])part(cushion,m,[x,.35,z],[1,1,1],[0,a,0]);
    for(const a of [-1.65,-.85,0,.85,1.65])part(ball,i===1?warm:paint[(i+1)%6],[x+1.47*Math.cos(a),.68,z+1.47*Math.sin(a)],[.12,.22,.24],[0,-a,0]);
    part(cyl,wood,[x,.29,z],[.40,.54,.40]);part(cyl,ceramic,[x,.585,z],[.64,.045,.64]);
    box([x-.18,.635,z+.10],[.31,.04,.23],dark,null,[0,.2,0]);box([x-.12,.669,z+.08],[.27,.025,.20],paint[i],null,[0,-.1,0]);plant(x+.21,z-.17,.41,.61);
    // Independent visitor chair in the opening, not a wall across access.
    part(ball,m,[x-1.40,.49,z+.75],[.30,.075,.28]);part(ball,m,[x-1.64,.74,z+.75],[.055,.29,.28]);
    for(const dx of [-.2,.2])for(const dz of [-.18,.18])stem([x-1.4+dx,.43,z+.75+dz],[x-1.4+dx*1.15,.05,z+.75+dz*1.15],.015,bronze);
  }
  meta('Three sea-facing discussion circles',{discussions,groups:3});
  // North hospitality wall: worktop, backbar, display shelves and varied stock.
  box([.15,.50,-8.16],[7.5,1,.70],wood);box([.15,1.02,-8.05],[7.62,.06,.92],ceramic);
  for(let i=0;i<38;i++)box([-3.5+i*.195,.49,-7.799],[.027,.89,.018],oak);
  box([.15,1.60,-8.69],[7.65,2.37,.075],wood);
  for(const y of [1.19,1.85,2.45])box([.15,y,-8.44],[7.58,.038,.43],bronze);
  const bottleGeo=geom(new T.LatheGeometry([new T.Vector2(.043,0),new T.Vector2(.050,.018),new T.Vector2(.05,.19),new T.Vector2(.022,.235),new T.Vector2(.018,.30),new T.Vector2(.020,.31)],12));
  const bottles=['#476f56','#946137','#4c7a88','#a56462','#bf9d57','#667963'].map(color=>material(color,.4,.15));
  for(let row=0;row<2;row++)for(let i=0;i<30;i++){
    const x=-3.38+i*.242,y=row?1.872:1.212,z=-8.35,h=.85+(i%4)*.09;
    part(bottleGeo,bottles[(i+row*2)%bottles.length],[x,y,z],[1,h,1]);part(cyl,bronze,[x,y+.31*h,z],[.022,.026,.022]);
    box([x,y+.12*h,z+.051],[.067,.075,.004],i%2?ceramic:dark);
  }
  // Espresso machine, two group heads, grinder, tea kettle, sink and glasses.
  box([-2.6,1.26,-8.03],[.84,.40,.46],dark);box([-2.6,1.31,-7.791],[.78,.18,.018],bronze);box([-2.6,1.077,-7.75],[.80,.03,.25],rubber);
  for(const x of [-2.8,-2.42]){part(cyl,bronze,[x,1.23,-7.77],[.055,.055,.055]);stem([x,1.22,-7.77],[x,1.22,-7.62],.016,dark);part(cyl,ceramic,[x,1.13,-7.72],[.045,.075,.045]);}
  box([-1.85,1.19,-8.05],[.22,.27,.25],bronze);part(cyl,dark,[-1.85,1.45,-8.05],[.10,.23,.10]);
  part(ball,ceramic,[-.86,1.19,-8.01],[.13,.15,.13]);stem([-.76,1.19,-8.01],[-.65,1.25,-8.01],.025,ceramic);
  box([.30,1.055,-8.03],[.62,.01,.38],dark);stem([.30,1.08,-8.24],[.30,1.39,-8.24],.018,bronze);stem([.30,1.39,-8.24],[.30,1.39,-8.03],.018,bronze);
  for(let i=0;i<10;i++)part(cyl,i%2?ceramic:bronze,[1.0+i*.20,1.115,-8.08],[.047,.12,.047]);
  for(const x of [-2.7,-1.2,.3]){part(cyl,dark,[x,.075,-6.95],[.28,.055,.28]);part(cyl,bronze,[x,.42,-6.95],[.028,.70,.028]);part(ball,cloth[0],[x,.79,-6.95],[.29,.075,.26]);part(ball,cloth[0],[x,.95,-6.73],[.28,.18,.045]);}
  meta('Tea coffee and drinks bar',{bottles:60,stools:3,espressoGroupHeads:2,tea:true,sink:true,bounds:[-3.66,3.96,-8.73,-7.59]});
  // Two low planted consoles leave a straight walk from the stair to all bays.
  for(const z of [-2,3.5]){box([-.3,.23,z],[.58,.46,1.1],wood);plant(-.3,z,.83,.46);}
  for(const z of [-7.7,7.9])plant(4.25,z,1.35);
  meta('Upper lounge clear circulation',{westEntry:[-4.95,0],clearWidthMetres:1.2,centralAisleX:[-2.55,-.8],style:'A'});
  for(const {g,m,matrices} of batches.values()){
    const mesh=new T.InstancedMesh(g,m,matrices.length);mesh.name='Lounge furniture batch';matrices.forEach((v,i)=>mesh.setMatrixAt(i,v));mesh.castShadow=true;mesh.receiveShadow=true;mesh.computeBoundingSphere();group.add(mesh);
  }
  return {group,dispose(){geos.forEach(g=>g.dispose());mats.forEach(m=>m.dispose());textures.forEach(t=>t.dispose());}};
}
