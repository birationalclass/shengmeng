import * as T from 'three';
import {VILLA_PLAN as PLAN} from './residence-plan.js?v76-villa';
import {RoundedBoxGeometry} from './vendor/geometries/RoundedBoxGeometry.js';
import {RESIDENCE as R} from './residence-layout.js?v76-villa';
import {BUILDING_SCALE as S} from './site-layout.js?v44-hall-clearance';
import {createRoofNumber} from './roof-number.js?v62-chalk-ink';
export function createResidence(scene,shared){
 const root=new T.Group();root.name='Sheng Meng coastal residence';root.position.fromArray(R.origin);scene.add(root);
 const owned=[],textures=[],geometries=new Set(),roofMetadata=[],batches=new Map(),dummy=new T.Object3D();
 const mat=(color,roughness=.75,extra={})=>{const m=new T.MeshStandardMaterial({color,roughness,...extra});owned.push(m);return m;};
 const stone=mat('#c5bba7',.86,{map:shared.stone.map,normalMap:shared.stone.normalMap,normalScale:new T.Vector2(.06,.06)}),wood=mat('#75604a',.78,{map:shared.timber.map,normalMap:shared.timber.normalMap,normalScale:new T.Vector2(.09,.09)}),plaster=mat('#e1d6bf',.91),dark=mat('#292d29',.62),bronze=mat('#9b8058',.4,{metalness:.65}),linen=mat('#cec5ae',.98,{normalMap:shared.pale.normalMap}),green=mat('#546b5d',.98),soil=mat('#454941',1),foliage=mat('#526a43',.93),light=mat('#dfbb7e',.5,{emissive:'#e8c48a',emissiveIntensity:.8});
 // Fine, low-contrast mineral pores / longitudinal wood grain, authored procedurally.
 function finishTexture(timber=false){const w=512,h=512,data=new Uint8Array(w*h*4);let seed=179;for(let y=0;y<h;y++)for(let x=0;x<w;x++){seed=(1664525*seed+1013904223)>>>0;const n=seed/4294967296-.5;const wave=timber?Math.sin(y*.8+Math.sin(x*.017)*2+Math.sin(y*.052)*5)*.035:Math.sin(y*.12+Math.sin(x*.01)*.5)*.012;const v=Math.max(0,Math.min(255,232+(wave+n*.035)*255)),k=(y*w+x)*4;data[k]=v;data[k+1]=v;data[k+2]=v;data[k+3]=255;}const t=new T.DataTexture(data,w,h);t.colorSpace=T.SRGBColorSpace;t.wrapS=t.wrapT=T.RepeatWrapping;t.magFilter=T.LinearFilter;t.minFilter=T.LinearMipmapLinearFilter;t.generateMipmaps=true;t.anisotropy=4;t.needsUpdate=true;textures.push(t);return t;}
 stone.map=finishTexture();stone.normalMap=null;wood.map=finishTexture(true);wood.normalMap=null;wood.color.set('#8b7355');
 const glass=new T.MeshPhysicalMaterial({color:'#d4e4df',roughness:.09,metalness:0,transparent:true,opacity:.10,depthWrite:false,side:T.DoubleSide});owned.push(glass);
 // Woven upholstery: restrained cross-warp relief, shared by cushions and rugs.
 const weaveData=new Uint8Array(128*128*4);for(let y=0;y<128;y++)for(let x=0;x<128;x++){const k=(y*128+x)*4,v=238+((x%4<2)=== (y%4<2)?5:-5);weaveData[k]=weaveData[k+1]=weaveData[k+2]=v;weaveData[k+3]=255;}const weave=new T.DataTexture(weaveData,128,128);weave.colorSpace=T.SRGBColorSpace;weave.wrapS=weave.wrapT=T.RepeatWrapping;weave.repeat.set(4,4);weave.magFilter=T.LinearFilter;weave.minFilter=T.LinearMipmapLinearFilter;weave.generateMipmaps=true;weave.needsUpdate=true;textures.push(weave);linen.map=weave;green.map=weave;
 const water=mat('#416967',.19,{metalness:.18,normalMap:shared.stone.normalMap,normalScale:new T.Vector2(.025,.025)});
 const islandGeometry=new T.CylinderGeometry(1,.96,1,128);geometries.add(islandGeometry);const shore=islandGeometry.attributes.position;for(let i=0;i<shore.count;i++){const x=shore.getX(i),z=shore.getZ(i),a=Math.atan2(z,x),k=.965+.018*Math.sin(3*a)+.012*Math.cos(5*a);shore.setXYZ(i,x*k,shore.getY(i),z*k);}islandGeometry.computeVertexNormals();
 const cube=new T.BoxGeometry(1,1,1),cylinder=new T.CylinderGeometry(1,1,1,20),sphere=new T.SphereGeometry(1,12,8);geometries.add(cube);geometries.add(cylinder);geometries.add(sphere);
 function piece(g,m,p,s=[1,1,1],rot=[0,0,0]){const key=g.uuid+m.uuid;if(!batches.has(key))batches.set(key,{g,m,matrices:[]});dummy.position.fromArray(p);dummy.scale.fromArray(s);dummy.rotation.set(...rot);dummy.updateMatrix();batches.get(key).matrices.push(dummy.matrix.clone());}
 const box=(p,s,m=stone,rot)=>piece(cube,m,p,s,rot);
 const rounded=new Map();function soft(p,s,m=linen,r=[0,0,0]){const key=s.join(',');if(!rounded.has(key)){const g=new RoundedBoxGeometry(...s,4,Math.min(...s)*.42);rounded.set(key,g);geometries.add(g);}piece(rounded.get(key),m,p,[1,1,1],r);}
 function plaque(title,lines,p,w=3,h=1.25,rotation=0){const c=document.createElement('canvas');c.width=1536;c.height=Math.round(1536*h/w);const ctx=c.getContext('2d');ctx.fillStyle='#e5ddc9';ctx.fillRect(0,0,c.width,c.height);ctx.fillStyle='#263c35';ctx.font='52px Georgia, serif';ctx.fillText(title,70,90);ctx.font='30px Georgia, serif';let y=155;for(const line of lines){const words=line.split(' ');let text='';for(const word of words){if(ctx.measureText(text+' '+word).width>1390){ctx.fillText(text,70,y);y+=42;text=word;}else text+=(text?' ':'')+word;}ctx.fillText(text,70,y);y+=48;}const texture=new T.CanvasTexture(c);texture.colorSpace=T.SRGBColorSpace;texture.anisotropy=4;textures.push(texture);const m=new T.MeshStandardMaterial({map:texture,roughness:.92});owned.push(m);const g=new T.PlaneGeometry(w,h);geometries.add(g);const mesh=new T.Mesh(g,m);mesh.position.fromArray(p);mesh.rotation.y=rotation;mesh.name='Residence plaque '+title;root.add(mesh);box([p[0],p[1],p[2]-.035],[w+.08,h+.08,.06],bronze);return mesh;}
 // Rounded dry island, layered retaining wall and a continuous stone plinth.
 piece(islandGeometry,soil,[0,-1.3,0],[55,3.6,43]);piece(islandGeometry,foliage,[0,.52,0],[54.8,.08,42.8]);
 box([3,.48,2],[59,.70,43],stone);box([3,.30,2],[59.5,.10,43.5],dark);
 // A dimensioned courtyard plan: four wings, 2 m passages and real door openings.
 const F=PLAN.floor;
 function slab(x,z,w,d,h=3.6){box([x,F-.12,z],[w,.24,d],stone);box([x,F+h+.15,z],[w+1.4,.30,d+1.4],stone);box([x,F+h-.035,z],[w-.15,.07,d-.15],plaster);box([x,F+h+.32,z],[w+.9,.05,d+.9],dark);
  for(const sx of [-1,1])box([x+sx*(w/2+.5),F+h+.08,z],[.06,.08,d+1.15],bronze);
 }
 for(const [x,z,w,d,h] of PLAN.roofs)slab(x,z,w,d,h);
 // Walls are assembled around openings; lintels never fill the doorway.
 function wall(axis,at,start,end,h=3.6,openings=[],m=plaster){let cursor=start;for(const [center,width,height=PLAN.doorHeight,sill=0] of [...openings].sort((a,b)=>a[0]-b[0])){segment(cursor,center-width/2,0,h);segment(center-width/2,center+width/2,0,sill);segment(center-width/2,center+width/2,sill+height,h);cursor=center+width/2;}segment(cursor,end,0,h);function segment(a,b,bottom,top){if(b-a<.005||top-bottom<.005)return;box(axis==='x'?[(a+b)/2,F+(top+bottom)/2,at]:[at,F+(top+bottom)/2,(a+b)/2],axis==='x'?[b-a,top-bottom,PLAN.wall]:[PLAN.wall,top-bottom,b-a],m);}}
 function glassWall(axis,at,start,end,h=3.6,gap=null,sill=0){const base=F+sill;const spans=gap?[[start,gap[0]],[gap[1],end]]:[[start,end]];for(const [a,b]of spans){const n=Math.ceil((b-a)/2.5);for(let i=0;i<n;i++){const lo=a+(b-a)*i/n,hi=a+(b-a)*(i+1)/n,mid=(lo+hi)/2;box(axis==='x'?[mid,base+h/2,at]:[at,base+h/2,mid],axis==='x'?[hi-lo-.065,h-.10,.025]:[.025,h-.10,hi-lo-.065],glass);box(axis==='x'?[lo,base+h/2,at]:[at,base+h/2,lo],axis==='x'?[.055,h,.10]:[.10,h,.055],bronze);}for(const y of [base+.025,base+h-.025])box(axis==='x'?[(a+b)/2,y,at]:[at,y,(a+b)/2],axis==='x'?[b-a,.05,.13]:[.13,.05,b-a],bronze);box(axis==='x'?[b,base+h/2,at]:[at,base+h/2,b],axis==='x'?[.055,h,.10]:[.10,h,.055],bronze);}}
 function doorway(axis,at,center,width=1.2){for(const offset of [-width/2,width/2])box(axis==='x'?[center+offset,F+1.4,at]:[at,F+1.4,center+offset],axis==='x'?[.06,2.8,.34]:[.34,2.8,.06],wood);box(axis==='x'?[center,F+2.82,at]:[at,F+2.82,center],axis==='x'?[width+.1,.065,.34]:[.34,.065,width+.1],wood);}
 wall('x',-14,-18,6,3.6,[]);wall('x',-14,6,18,4.8,[]);
 wall('z',-18,-14,14,3.6,[[-9,6,2.7,.5],[0,4,1.3,2.0],[9,7,2.9,.2]],stone);
 for(const [a,b,h,sill]of [[-12,-6,2.7,.5],[-2,2,1.3,2.0],[5.5,12.5,2.9,.2]]){glassWall('z',-18.02,a,b,h,null,sill);}
 glassWall('z',18,-14,14,4.8);glassWall('x',14,6,18,4.8);glassWall('x',14,-18,-6,3.6);
 wall('x',14,-6,6,3.6,[[2,2.4,3.0,0]],stone);doorway('x',14,2,2.4);
 // The open courtyard is enclosed by a continuous glass ribbon and sliding openings.
 glassWall('z',-6,-6,6,3.6,[-1,1]);glassWall('z',6,-6,6,4.8,[-1,1]);glassWall('x',-6,-6,6,3.6,[-1,1]);glassWall('x',6,-6,6,3.6,[-1,1]);
 wall('z',-8,-14,14,3.6,[[-8,1.4],[0,1.2],[9,1.4]],wood);for(const z of [-8,0,9])doorway('z',-8,z,z===0?1.2:1.4);
 wall('x',-4,-18,-8,3.6,[]);wall('x',4,-18,-8,3.6,[[-10.5,1.2]]);doorway('x',4,-10.5);
 wall('z',-13,-4,4,3.6,[[0,1.2]]);doorway('z',-13,0);
 wall('x',-6,8,18,4.8,[[10,1.4]]);doorway('x',-6,10,1.4);
 wall('z',14,-6,3,4.8,[[-1,2.0]],wood);doorway('z',14,-1,2);
 wall('z',-2,6,14,3.6,[[8,1.2],[12,1.1]]);wall('x',10,-6,-2,3.6,[]);for(const z of [8,12])doorway('z',-2,z,z===8?1.2:1.1);
 // Recessed plinths, panel joints, roof shadow gaps, 6 m structural rhythm.
 for(const x of [-18,-6,6,18])for(const z of [-14,-6,6,14]){if(Math.abs(x)===6&&Math.abs(z)===6)continue;const h=x>=6?4.8:3.6;box([x,F+h/2,z],[.24,h,.24],stone);}
 for(let z=-13.5;z<14;z+=1.2)box([-18.16,2.8,z],[.012,3.4,.008],dark);
 for(let x=-17.5;x<6;x+=1.2)box([x,2.8,-14.15],[.008,3.4,.012],dark);
 for(const [x,z,w,d,h]of PLAN.roofs){box([x,F+h-.1,z-d/2+.35],[w-.8,.018,.06],light);box([x,F+.065,z-d/2+.18],[w-.4,.13,.035],wood);}
 // Timber parquet uses jointed planks at a consistent physical scale.
 const oak=[wood,mat('#92795b',.83,{map:wood.map}),mat('#968064',.82,{map:wood.map}),mat('#887257',.85,{map:wood.map})];
 for(const [x0,x1,z0,z1]of [[-17.8,-8.2,-13.8,-4.2],[-17.8,-8.2,4.2,13.8],[6.2,17.8,3.2,13.8],[6.2,17.8,-13.8,-6.2]])for(let x=x0;x<x1-.05;x+=.24)for(let z=z0;z<z1-.05;z+=2.0){const w=Math.min(.233,x1-x),d=Math.min(1.993,z1-z);box([x+w/2,F+.009,z+d/2],[w,.015,d],oak[Math.abs(Math.floor(x*13+z*7))%4]);}
 function table(x,z,w,d,y=F+.75,m=wood){soft([x,y,z],[w,.09,d],m);for(const dx of [-w*.39,w*.39])for(const dz of [-d*.34,d*.34])box([x+dx,(y+F)/2,z+dz],[.05,y-F,.05],bronze);}
 function chair(x,z,r=0){const c=Math.cos(r),s=Math.sin(r),pos=(dx,y,dz)=>[x+c*dx+s*dz,y,z-s*dx+c*dz];soft(pos(0,F+.45,0),[.56,.13,.56],linen,[0,r,0]);soft(pos(0,F+.76,-.24),[.56,.55,.1],green,[0,r,0]);for(const dx of [-.22,.22])for(const dz of [-.20,.20])box(pos(dx,F+.21,dz),[.035,.42,.035],bronze);}
 function sofa(x,z,w,r=0){const c=Math.cos(r),s=Math.sin(r),pos=(dx,y,dz)=>[x+c*dx+s*dz,y,z-s*dx+c*dz];soft(pos(0,F+.34,0),[w,.36,1.02],linen,[0,r,0]);soft(pos(0,F+.68,-.43),[w,.80,.21],linen,[0,r,0]);for(const dx of [-w/2+.12,w/2-.12])soft(pos(dx,F+.58,0),[.24,.72,1.04],linen,[0,r,0]);for(let i=0;i<3;i++){soft(pos((i-1)*w*.26,F+.54,.05),[w*.29,.12,.75],linen,[0,r,0]);soft(pos((i-1)*w*.25,F+.77,-.22),[.46,.44,.13],green,[0,r,.07*(i-1)]);}for(const dx of [-w*.4,w*.4])box(pos(dx,F+.09,0),[.10,.18,.65],dark);}
 function vase(x,z,y,size=.18){piece(cylinder,bronze,[x,y+size*.4,z],[size*.7,size*.8,size*.7]);piece(sphere,plaster,[x,y+size,z],[size,size*.85,size]);}
 function book(x,z,y,w=.28,d=.36,m=wood){box([x,y,z],[w,.045,d],m);box([x,y+.027,z],[w*.96,.018,d*.96],plaster);}
 function lamp(x,z,y){piece(cylinder,bronze,[x,y+.22,z],[.014,.44,.014]);piece(cylinder,linen,[x,y+.47,z],[.19,.22,.19]);piece(cylinder,bronze,[x,y,z],[.14,.025,.14]);}
 // Library millwork: bays, shelf lips, brass dividers, individually varied books.
 const bookColors=['#697465','#a58b68','#b6b0a2','#536873','#7d6255','#d5c6a7'].map(c=>mat(c,.92));
 for(let bay=0;bay<6;bay++){const x=-17.1+bay*1.45;box([x,F+1.7,-13.70],[1.4,3.4,.28],wood);for(const dx of [-.70,.70])box([x+dx,F+1.7,-13.46],[.035,3.4,.60],bronze);box([x,F+.3,-13.35],[1.38,.6,.60],wood);for(let row=0;row<5;row++){const y=F+.7+row*.50;box([x,y,-13.40],[1.4,.035,.62],wood);box([x,y+.025,-13.075],[1.4,.015,.015],bronze);for(let j=0;j<9;j++){const h=.24+((j*7+row*3+bay)%9)*.016;const xx=x-.6+j*.145;box([xx,y+h/2+.027,-13.27],[.07+(j%3)*.018,h,.30],bookColors[(bay+j+row)%6],[0,0,j%7===0?.08:0]);box([xx,y+h*.72,-13.11],[.055,.009,.008],bronze);}}}
 table(-12,-10,2.8,1.15);chair(-12,-8.95);book(-12.6,-10,F+.84);book(-11.4,-10,F+.83,.34,.44,green);lamp(-13,-10.1,F+.81);plaque('SHENG MENG',['ALGEBRAIC GEOMETRY'],[-11.9,F+1.16,-10.5],.85,.28);
 sofa(-14,-6,2.5);table(-14,-7.3,1.4,.65,F+.40,stone);book(-14.2,-7.3,F+.48);box([-13,F+.025,-7.8],[6,.035,4.4],linen);
 // Gallery wall panels and sculpture plinths retain the mathematical collection.
 for(const [i,title]of ['DYNAMICS','BUNDLES','PASCAL'].entries()){const x=-4+i*4;box([x,F+1.85,-13.72],[3.1,3.35,.06],wood);plaque(title,['MATHEMATICAL STRUCTURES'],[x,F+2.4,-13.67],2.7,.65);box([x,F+.48,-11.7],[1.15,.96,1.15],stone);const g=i===0?new T.TorusKnotGeometry(.36,.028,128,12,2,3):i===1?new T.TorusGeometry(.40,.045,12,80):new T.IcosahedronGeometry(.45,0);geometries.add(g);piece(g,bronze,[x,F+1.45,-11.7]);}
 // Studio: two work places, acoustic slats, display and low storage.
 for(let x=7;x<17.6;x+=.18)box([x,F+1.85,-13.70],[.07,3.65,.12],wood);
 for(const x of [10,14]){table(x,-11,2.4,1.0);chair(x,-10.0);box([x,F+1.25,-11.35],[1.2,.73,.045],dark);box([x,F+.95,-11.35],[.04,.35,.06],bronze);box([x,F+.83,-10.9],[.56,.025,.18],dark);plaque('AI4MATH',['PROOF / DISCOVERY'],[x,F+1.25,-11.323],1.10,.65);lamp(x-.9,-11.1,F+.81);}
 box([16.8,F+.45,-8.1],[1.6,.90,2.6],wood);for(let z=-9.1;z<-7;z+=.6)box([16,F+.52,z],[.012,.60,.012],dark);plaque('CREATIVE LAB',['msreader / AI4Games'],[13,F+3,-13.60],3.1,.8);
 // Living room with opposed seating, hearth, paired low tables and pendant rings.
 box([11.5,F+.028,8.5],[8.0,.045,6.9],linen);sofa(11.5,6,3.6);sofa(11.5,11,3.6,Math.PI);chair(15,8.5,-Math.PI/2);table(11,8.4,1.4,1.4,F+.34,stone);table(12.5,8.9,1.1,1.1,F+.43,wood);book(10.8,8.4,F+.42);vase(12.5,8.9,F+.48);
 box([6.3,F+2.1,10.3],[.36,4.2,4.7],stone);box([6.51,F+.65,10.3],[.025,.45,3.1],dark);box([6.54,F+.50,10.3],[.018,.018,2.4],light);box([6.8,F+.2,10.3],[1,.4,5],stone);
 for(const [r,y]of [[1.4,4.65],[.95,4.38]]){const g=new T.TorusGeometry(r,.025,8,96);geometries.add(g);piece(g,bronze,[11.5,y,8.4],[1,1,1],[Math.PI/2,0,0]);piece(g,light,[11.5,y-.025,8.4],[1,1,1],[Math.PI/2,0,0]);}for(const x of [10.5,12.5])piece(cylinder,bronze,[x,5.1,8.4],[.007,1,.007]);
 // Dining and separate kitchen / service core, with counters and real clear aisles.
 table(10.8,-1.7,2.1,3.3,F+.76);for(const z of [-2.85,-1.7,-.55]){chair(9.15,z,-Math.PI/2);chair(12.45,z,Math.PI/2);}for(const z of [-3.95,.55])chair(10.8,z,z<0?0:Math.PI);vase(10.8,-1.7,F+.83,.17);
 box([17.35,F+.45,-1.5],[.8,.9,8.1],wood);box([17.3,F+.93,-1.5],[.92,.06,8.2],stone);for(let z=-5.2;z<2.5;z+=.6)box([16.94,F+.46,z],[.008,.75,.014],dark);box([17.3,F+.99,-3.8],[.55,.015,1.0],dark);for(const z of [-4,-3.6])piece(cylinder,dark,[17.3,F+1.01,z],[.12,.01,.12]);box([17.3,F+.98,.9],[.58,.035,.75],dark);piece(cylinder,bronze,[17.53,F+1.2,1.1],[.018,.42,.018]);box([17.4,F+1.4,1.1],[.27,.025,.025],bronze);
 box([15.5,F+.46,-3.5],[1.1,.92,2.0],wood);box([15.5,F+.96,-3.5],[1.2,.07,2.1],stone);box([15.5,F+1.7,-5.55],[2,3.4,.65],wood);for(const x of [15,16])box([x,F+1.45,-5.20],[.025,.7,.025],bronze);
 // Private suite: bedroom, walk-through wardrobe and enclosed spa bathroom.
 box([-13,F+.20,9],[2.35,.4,2.55],wood);soft([-13,F+.5,9],[2.20,.30,2.4],linen);soft([-13,F+.72,9.5],[2.2,.09,1.35],green);soft([-13,F+1.05,7.72],[5.8,1.7,.17],linen);for(const x of [-13.6,-12.4])soft([x,F+.76,8.3],[.95,.17,.55],plaster);for(const x of [-15,-11]){table(x,8.2,.85,.60,F+.55);lamp(x,8.2,F+.62);}box([-13,F+.028,9.5],[6,.035,5.2],linen);soft([-13,F+.45,11.5],[1.8,.4,.5],green);chair(-16,11.4,.5);table(-16,12.2,.7,.7,F+.48,stone);
 for(const x of [-12.65,-8.4]){box([x,F+1.55,0],[.60,3.1,6.8],wood);for(let z=-3;z<=3;z+=.75){box([x+(x<-10?.31:-.31),F+1.6,z],[.008,2.8,.012],dark);}}box([-10.5,F+.48,0],[1.1,.96,2.2],wood);box([-10.5,F+.98,0],[1.15,.05,2.25],stone);
 box([-16.7,F+.78,2.7],[2.1,.14,.9],stone);for(const x of [-17.25,-16.1]){piece(cylinder,plaster,[x,F+.91,2.7],[.33,.16,.26]);piece(cylinder,bronze,[x,F+1.1,2.35],[.015,.5,.015]);}box([-16.7,F+1.85,3.7],[2.7,1.6,.045],glass);box([-16.7,F+1.85,3.73],[2.75,1.65,.015],bronze);
 soft([-15.4,F+.30,-1.8],[1.75,.6,2.5],plaster);soft([-15.4,F+.61,-1.8],[1.45,.025,2.16],water);glassWall('x',.4,-17.8,-15.0,2.4);piece(cylinder,bronze,[-17.5,F+1.25,-2.8],[.018,2.5,.018]);piece(cylinder,bronze,[-17.2,F+2.48,-2.8],[.18,.025,.18]);box([-17.4,F+.02,-2],[.7,.018,2.8],stone);
 // Entry axis opens directly through the court; coat storage and guest WC stay tucked away.
 box([-4,F+1.4,6.3],[3.6,2.8,.50],wood);box([-4,F+.48,8.9],[2.8,.96,.60],wood);soft([-4,F+.99,8.9],[2.8,.10,.60],linen);
 box([-4,F+.73,13.4],[2.7,.13,.6],stone);piece(cylinder,plaster,[-4,F+.85,13.4],[.28,.14,.22]);soft([-5,F+.23,11.5],[.40,.46,.62],plaster);soft([-5,F+.52,11.3],[.43,.12,.55],plaster);
 table(3.8,10,1.0,2.2,F+.80,stone);vase(3.8,10.6,F+.87,.25);plaque('SHENG MENG',['NUS 2013–18 / MPIM 2018–19','KIAS 2019–22 / ECNU 2022–'],[-.9,F+2.15,13.80],3.0,1.05);
 // Covered arrival bridge and a garden which is deliberately not a circular lawn.
 box([2,3.9,17],[5.2,.20,7],wood);for(const x of [-.4,4.4])box([x,2.3,20],[.16,3.8,.16],bronze);for(let z=15;z<=31;z+=1.22)box([2,.78-(z-15)*.013,z],[4.5,.16,1.17],stone);
 box([0,F-.03,0],[11.5,.06,11.5],soil);for(const x of [-4.9,4.9])box([x,F+.02,0],[1.0,.10,11.5],stone);for(const z of [-4.9,4.9])box([0,F+.02,z],[8.8,.10,1.0],stone);
 box([1,F+.04,0],[4,.16,5.0],dark);box([1,F+.13,0],[3.8,.012,4.8],water);box([-2.6,F+.23,2.0],[2.2,.5,4.0],soil);
 function tree(x,z,scale=1){piece(cylinder,wood,[x,.6+1.5*scale,z],[.08*scale,3*scale,.08*scale]);for(let i=0;i<19;i++){const a=i*2.399,r=.6+.06*(i%7);piece(sphere,foliage,[x+Math.cos(a)*r*scale,.6+(3+Math.sin(i*.9)*.55)*scale,z+Math.sin(a)*r*scale],[.85*scale,.42*scale,.7*scale]);}}
 tree(-2.6,1.5,1.1);for(const [x,z,s]of [[-25,-17,1.6],[-26,13,1.8],[25,-20,1.7],[32,20,1.5],[8,31,1.6]])tree(x,z,s);
 // Infinity pool: coping, overflow slot, submerged steps and continuous deck.
 box([25,-.5,0],[8,1.35,24],stone);box([25,.86,0],[7.4,.012,23.4],water);for(const x of [20.9,29.1])box([x,.94,0],[.30,.22,24.6],stone);for(const z of [-12.2,12.2])box([25,.94,z],[8.5,.22,.30],stone);box([29.32,.81,0],[.12,.14,24],dark);for(let i=0;i<4;i++)box([25,.70-i*.22,-10.8+i*.45],[6.7,.15,.45],stone);
 for(let z=-12;z<14;z+=1.2)box([19.8,.86,z],[1.1,.045,1.17],stone);
 for(let x=6;x<18;x+=.35)box([x,4.05,18.3],[.065,.18,6.5],wood);for(const x of [6,18])for(const z of [15.5,21.1])box([x,2.5,z],[.14,3.2,.14],bronze);
 table(10,18.2,2.8,1.1);for(const x of [9,11]){chair(x,17.2);chair(x,19.2,Math.PI);}vase(10,18.2,F+.82);
 for(const x of [23,26]){soft([x,F+.28,16.5],[.85,.23,2.15],linen);soft([x,F+.58,15.65],[.85,.72,.18],linen,[.45,0,0]);box([x,F+.10,16.5],[.9,.18,2.25],wood);}
 for(let i=0;i<6;i++)box([34+i*1.5,.60-i*.10,12],[1.55,.18,3],stone);box([45,-.03,12],[8,.24,4],wood);
 // Layered planting / stone clusters, low garden walls and subtle path lights.
 for(const [cx,cz]of [[-35,-15],[-28,24],[32,-24],[39,11],[-5,-29]])for(let i=0;i<9;i++){const a=i*2.399,r=1.5+(i%4);piece(sphere,i%3?foliage:stone,[cx+Math.cos(a)*r,.30+(i%3)*.12,cz+Math.sin(a)*r],[1.1+(i%3)*.5,.55+(i%2)*.3,.9+(i%4)*.3]);}
 for(let i=0;i<90;i++){const a=i*2.399,r=27+(i%11)*1.1,x=Math.cos(a)*r,z=Math.sin(a)*r*.77;if(Math.abs(x)<20&&Math.abs(z)<22)continue;piece(sphere,foliage,[x,.63,z],[.55,.18,.43]);}
 for(const z of [22,26,30])for(const x of [-1,5]){box([x,.90,z],[.07,.65,.07],bronze);box([x,1.18,z],[.08,.045,.08],light);}
 for(const {g,m,matrices}of batches.values()){const mesh=new T.InstancedMesh(g,m,matrices.length);matrices.forEach((v,i)=>mesh.setMatrixAt(i,v));mesh.castShadow=m!==glass;mesh.receiveShadow=true;mesh.name='Residence material batch';mesh.computeBoundingSphere();root.add(mesh);}
 const number=createRoofNumber(root,10,12,F+4.8+.36,0,12,28);
 for(const [x,z,w,d,h]of PLAN.roofs){const metadata=new T.Object3D();metadata.name='Residence dry room';metadata.userData={bounds:[(R.origin[0]+x-w/2)/S,(R.origin[0]+x+w/2)/S,(z-d/2)/S,(z+d/2)/S],floorY:F/S,clearHeight:h+.3};scene.add(metadata);roofMetadata.push(metadata);}
 const points=[];for(const [x,y,z,power]of [[12,4.8,8,130],[-13,3.7,-8,90],[-13,3.7,9,65],[0,3.7,-10,75]]){const p=new T.PointLight('#ffe4bb',power,18,2);p.position.set(x,y,z);p.userData.power=power;root.add(p);points.push(p);}root.updateMatrixWorld(true);root.userData.plan=PLAN;
 return {root,update(camera,day){const close=camera.position.distanceTo(root.position)<180;for(const p of points){p.visible=close;p.intensity=p.userData.power*(1-.35*day);}light.emissiveIntensity=.3+(1-day)*.8;},dispose(){number.dispose();geometries.forEach(g=>g.dispose());textures.forEach(t=>t.dispose());owned.forEach(m=>m.dispose());roofMetadata.forEach(m=>scene.remove(m));scene.remove(root);}};
}
