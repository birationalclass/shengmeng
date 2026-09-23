import * as T from 'three';
import {RoundedBoxGeometry} from './vendor/geometries/RoundedBoxGeometry.js';
import {RESIDENCE as R} from './residence-layout.js?v73-residence';
import {BUILDING_SCALE as S} from './site-layout.js?v44-hall-clearance';
import {createRoofNumber} from './roof-number.js?v62-chalk-ink';
export function createResidence(scene,shared){
 const root=new T.Group();root.name='Sheng Meng coastal residence';root.position.fromArray(R.origin);scene.add(root);
 const owned=[],textures=[],geometries=new Set(),roofMetadata=[],batches=new Map(),dummy=new T.Object3D();
 const mat=(color,roughness=.75,extra={})=>{const m=new T.MeshStandardMaterial({color,roughness,...extra});owned.push(m);return m;};
 const stone=mat('#c5bba7',.86,{map:shared.stone.map,normalMap:shared.stone.normalMap,normalScale:new T.Vector2(.06,.06)}),wood=mat('#75604a',.78,{map:shared.timber.map,normalMap:shared.timber.normalMap,normalScale:new T.Vector2(.09,.09)}),plaster=mat('#e1d6bf',.91),dark=mat('#292d29',.62),bronze=mat('#9b8058',.4,{metalness:.65}),linen=mat('#cec5ae',.98,{normalMap:shared.pale.normalMap}),green=mat('#546b5d',.98),soil=mat('#454941',1),foliage=mat('#526a43',.93),light=mat('#dfbb7e',.5,{emissive:'#e8c48a',emissiveIntensity:.8});
 const glass=new T.MeshPhysicalMaterial({color:'#d4e4df',roughness:.09,metalness:0,transparent:true,opacity:.10,depthWrite:false,side:T.DoubleSide});owned.push(glass);
 const water=mat('#416967',.19,{metalness:.18,normalMap:shared.stone.normalMap,normalScale:new T.Vector2(.025,.025)});
 const islandGeometry=new T.CylinderGeometry(1,.96,1,128);geometries.add(islandGeometry);const shore=islandGeometry.attributes.position;for(let i=0;i<shore.count;i++){const x=shore.getX(i),z=shore.getZ(i),a=Math.atan2(z,x),k=.965+.018*Math.sin(3*a)+.012*Math.cos(5*a);shore.setXYZ(i,x*k,shore.getY(i),z*k);}islandGeometry.computeVertexNormals();
 const cube=new T.BoxGeometry(1,1,1),cylinder=new T.CylinderGeometry(1,1,1,20),sphere=new T.SphereGeometry(1,12,8);geometries.add(cube);geometries.add(cylinder);geometries.add(sphere);
 function piece(g,m,p,s=[1,1,1],rot=[0,0,0]){const key=g.uuid+m.uuid;if(!batches.has(key))batches.set(key,{g,m,matrices:[]});dummy.position.fromArray(p);dummy.scale.fromArray(s);dummy.rotation.set(...rot);dummy.updateMatrix();batches.get(key).matrices.push(dummy.matrix.clone());}
 const box=(p,s,m=stone,rot)=>piece(cube,m,p,s,rot);
 const rounded=new Map();function soft(p,s,m=linen,r=[0,0,0]){const key=s.join(',');if(!rounded.has(key)){const g=new RoundedBoxGeometry(...s,2,Math.min(...s)*.18);rounded.set(key,g);geometries.add(g);}piece(rounded.get(key),m,p,[1,1,1],r);}
 function plaque(title,lines,p,w=3,h=1.25,rotation=0){const c=document.createElement('canvas');c.width=1536;c.height=Math.round(1536*h/w);const ctx=c.getContext('2d');ctx.fillStyle='#e5ddc9';ctx.fillRect(0,0,c.width,c.height);ctx.fillStyle='#263c35';ctx.font='52px Georgia, serif';ctx.fillText(title,70,90);ctx.font='30px Georgia, serif';let y=155;for(const line of lines){const words=line.split(' ');let text='';for(const word of words){if(ctx.measureText(text+' '+word).width>1390){ctx.fillText(text,70,y);y+=42;text=word;}else text+=(text?' ':'')+word;}ctx.fillText(text,70,y);y+=48;}const texture=new T.CanvasTexture(c);texture.colorSpace=T.SRGBColorSpace;texture.anisotropy=4;textures.push(texture);const m=new T.MeshStandardMaterial({map:texture,roughness:.92});owned.push(m);const g=new T.PlaneGeometry(w,h);geometries.add(g);const mesh=new T.Mesh(g,m);mesh.position.fromArray(p);mesh.rotation.y=rotation;mesh.name='Residence plaque '+title;root.add(mesh);box([p[0],p[1],p[2]-.035],[w+.08,h+.08,.06],bronze);return mesh;}
 // Rounded dry island, layered retaining wall and a continuous stone plinth.
 piece(islandGeometry,soil,[0,-1.3,0],[55,3.6,43]);piece(islandGeometry,foliage,[0,.52,0],[54.8,.08,42.8]);
 box([0,.48,2],[49,.70,39],stone);box([0,.78,1],[43,.12,31],stone);box([0,.30,2],[49.5,.10,39.5],dark);
 // Paving joints stay on a single grid and do not overlap the villa floor.
 for(let x=-24;x<=24;x+=2)box([x,.84,20],[.012,.01,5],dark);
 for(let z=-17;z<=22;z+=2)for(const x of [-23,23])box([x,.84,z],[2,.01,.012],dark);
 // Three inhabited wings around an open planted courtyard; a high living pavilion.
 const wings=[[-13.5,-8.5,13,11,4.1],[-13.5,7,13,20,4.1],[6.5,-8.5,27,11,4.1],[10,5.5,20,17,5.4]];
 for(const [x,z,w,d,h] of wings){box([x,R.floor-.1,z],[w,.2,d],wood);box([x,R.floor+h,z],[w+.8,.23,d+.8],stone);box([x,R.floor+h-.15,z],[w-.25,.05,d-.25],plaster);for(const sx of [-1,1])box([x+sx*(w/2-.12),R.floor+h/2,z],[.24,h,d],sx===-1&&x<0?plaster:glass);}
 // North solid back wall, living facade with genuine open arrival gap.
 box([0,2.95,-14],[40,4.1,.3],plaster);box([-20,2.95,1.5],[.30,4.1,31],stone);
 for(const [x,w] of [[-13.5,13],[3,6],[16,8]]){box([x,3.5,14],[w,5.2,.035],glass);for(const xx of [x-w/2,x+w/2])box([xx,3.5,14],[.07,5.2,.09],bronze);box([x,1,14],[w,.07,.12],bronze);}
 for(let z=-13;z<14;z+=2.7)box([20,3.5,z],[.065,5.2,.07],bronze);
 // Slim external timber screen, shadow gaps, sill and fascia details.
 for(let x=-19.7;x<-7;x+=.38)box([x,3.03,17.5],[.10,4.25,.20],wood);
 for(let z=-13.5;z<16.5;z+=.40)box([-20.4,3,z],[.16,4.2,.08],wood);
 for(const z of [-13.7,13.7])box([10,5.98,z],[19,.035,.045],light);
 box([6.5,5.14,-8.5],[27.8,.06,11.8],dark);box([10,6.47,5.5],[20.8,.06,17.8],dark);
 // Entry canopy, stepping stones, arrival bench and brass nameplate.
 box([9,4.3,17.3],[5,.16,6.5],wood);for(const x of [6.6,11.4])box([x,2.55,20],[.12,3.5,.12],bronze);
 for(let z=22;z<=35;z+=2.1)box([9,.6-(z-22)*.02,z],[4.4,.18,1.6],stone);
 soft([3,1.3,15.5],[3.8,.30,.8],wood);for(const x of [1.6,4.4])box([x,1.05,15.5],[.12,.3,.5],bronze);
 plaque('SHENG MENG',['MATHEMATICS / A PRIVATE RETREAT'],[4.4,2.7,14.08],3.1,.72);
 // Open garden, a sculptural olive and gravel-lined water basin.
 box([-3.4,1,4.3],[5.8,.22,11],soil);piece(cylinder,wood,[-3.5,3,3.5],[.14,4,.14]);for(let i=0;i<9;i++){const a=i*2.4;piece(sphere,foliage,[-3.5+Math.cos(a)*1.1,4.4+Math.sin(i)*.45,3.5+Math.sin(a)*1.1],[1.25,.62,1]);}
 box([27,.82,0],[8,.35,23],dark);box([27,1.01,0],[7.6,.018,22.6],water);for(const x of [22.7,31.3])box([x,1,0],[.30,.30,23.6],stone);
 function sofa(x,z,w,rot=0){soft([x,1.38,z],[w,.48,1.02],linen,[0,rot,0]);soft([x,1.85,z-.4],[w,.80,.24],linen,[0,rot,0]);for(const dx of [-w/2+.15,w/2-.15])soft([x+dx,1.65,z],[.25,.72,1.05],linen);for(let i=0;i<3;i++)soft([x-w*.32+i*w*.32,1.68,z-.30],[.50,.45,.20],green,[0,0,(i-1)*.10]);}
 function table(x,z,w=2.2,d=1.0,y=1.5){soft([x,y,z],[w,.09,d],wood);for(const dx of [-w*.38,w*.38])for(const dz of [-d*.34,d*.34])box([x+dx,(y+.9)/2,z+dz],[.055,y-.9,.055],bronze);}
 function chair(x,z){soft([x,1.35,z],[.58,.12,.6],green);soft([x,1.72,z-.24],[.58,.70,.1],green);for(const dx of [-.23,.23])for(const dz of [-.23,.23])box([x+dx,1.12,z+dz],[.04,.44,.04],bronze);}
 // Living pavilion, wool rug, long low hearth, books and ceramics.
 box([8,.92,5],[12,.025,8],green);sofa(6,3,4.7);sofa(12,8.6,3.7);table(8,6,3.4,1.7,1.25);
 box([1.3,1.4,-2.65],[5,.95,.5],stone);box([1.3,1.65,-2.36],[3.4,.24,.02],dark);box([1.3,1.56,-2.34],[2.7,.025,.02],light);
 piece(cylinder,bronze,[9.4,1.41,6],[.15,.23,.15]);piece(sphere,plaster,[9.4,1.6,6],[.22,.27,.22]);
 // Dining and fully modelled kitchen wall: fluted fronts, worktop and fittings.
 table(15,-.4,3.6,1.3,1.66);for(const x of [13.8,15,16.2]){chair(x,.7);chair(x,-1.5);}
 box([17,1.45,-11.8],[5,1.1,1],wood);box([17,2.02,-11.8],[5.15,.10,1.1],stone);for(let x=14.6;x<19.5;x+=.46){box([x,1.42,-11.27],[.015,.95,.02],dark);box([x+.18,1.87,-11.24],[.22,.02,.025],bronze);}box([18.7,3.05,-12.4],[1.25,4.1,1.2],dark);box([16.6,2.09,-11.7],[.85,.025,.65],dark);piece(cylinder,bronze,[16.9,2.26,-12],[.025,.40,.025]);box([16.75,2.46,-12],[.3,.03,.035],bronze);
 // Research library: articulated cabinet frame, individual book spines and desk.
 const bookColors=['#586b5d','#958264','#b7ac91','#445b65','#766659'].map(c=>mat(c,.94));
 for(let bay=0;bay<5;bay++){const x=-18.1+bay*2.0;box([x,2.75,-13.5],[1.92,3.6,.35],wood);for(let row=0;row<5;row++){const y=1.1+row*.67;box([x,y,-13.1],[1.9,.045,.6],wood);for(let j=0;j<10;j++){const height=.34+((bay*17+row*3+j*7)%9)*.022;box([x-.79+j*.16,y+height/2+.04,-13.03],[.10+(j%3)*.014,height,.34],bookColors[(j+row+bay)%5],[0,0,(j%6===0?.08:0)]);}}}
 table(-13,-8,5,1.9,1.68);chair(-13,-6.7);box([-11.6,1.78,-8],[.70,.06,.5],green);box([-14.3,1.75,-8],[.8,.025,.55],plaster);piece(cylinder,bronze,[-15,2.1,-8.5],[.022,.75,.022]);piece(cylinder,green,[-15,2.5,-8.5],[.35,.14,.35]);
 plaque('RESEARCH / ALGEBRAIC GEOMETRY',[],[-12.4,4.55,-12.72],4.4,.50);
 plaque('SHENG MENG',['East China Normal University','smeng@math.ecnu.edu.cn'],[-14.9,1.96,-8.98],1.4,.56);
 // Gallery: three mathematical sculptures in glazed, bronze-framed niches.
 for(const [i,title] of ['PASCAL','DYNAMICS','BUNDLES'].entries()){const x=-2+i*3.1;box([x,1.3,-11.2],[1.5,.8,1.4],stone);const g=i===0?new T.TorusKnotGeometry(.38,.025,100,8,2,3):i===1?new T.TorusGeometry(.40,.035,8,64):new T.SphereGeometry(.40,18,10);geometries.add(g);piece(g,bronze,[x,2.05,-11.2]);plaque(title,['VISUAL LAB'],[x,3.25,-13.78],2.1,.7);}
 box([1.3,3.1,-2.75],[5.8,4.4,.20],plaster);
 plaque('ACADEMIC JOURNEY',['2013–2018  National University of Singapore','2018–2019  Max Planck Institute for Mathematics','2019–2022  Korea Institute for Advanced Study','2022–present  East China Normal University'],[1.3,3.4,-2.63],5.5,1.75);
 // Studio desk, monitor housing, keyboard and a dedicated strategy table.
 table(10,-9,4.2,1.7,1.66);chair(10,-7.7);box([10,2.25,-9.5],[1.55,.92,.065],dark);box([10,1.88,-9.5],[.08,.38,.08],bronze);box([10,1.76,-8.8],[.68,.025,.24],dark);plaque('AI4MATH',['Proof / Discovery / Knowledge','msreader'],[10,2.25,-9.458],1.45,.80);
 plaque('CREATIVE LAB',['AI4Math / AI4Games','Endless / Frontier Claim'],[11,3.5,-13.78],3.8,1.2);
 // Bedroom, ensuite, wardrobe and privacy partition; no personal data invented.
 box([-13.6,1.10,6],[4.3,.26,3],wood);soft([-13.6,1.42,6],[4.15,.38,2.8],linen);soft([-13.6,1.91,4.65],[4.4,1.15,.24],green);soft([-13.6,1.65,6.6],[4.15,.10,1.55],green);for(const x of [-14.8,-12.5])soft([x,1.74,5.2],[1.5,.16,.65],plaster);for(const x of [-16.5,-10.6]){table(x,5.1,.8,.8,1.45);piece(cylinder,light,[x,1.88,5.1],[.20,.45,.20]);}
 box([-13.6,.93,7],[7,.035,6.6],linen);box([-17.9,2.75,1.1],[4.1,3.7,.14],wood);box([-17.9,1.8,-1.5],[3.6,.15,1.2],stone);piece(cylinder,plaster,[-17.9,1.95,-1.5],[.42,.16,.34]);box([-17.9,2.75,-2.12],[2.5,1.4,.035],glass);for(let x=-19.5;x<-7.5;x+=.55)box([x,2.4,16.1],[.5,2.9,.65],wood);
 // Shaded sea terrace with loungers, tea table, stepped dock and shoreline boulders.
 for(let x=4;x<=19;x+=.7)box([x,4.2,21],[.10,.20,7],wood);for(const x of [4,19])for(const z of [18,24])box([x,2.5,z],[.10,3.4,.10],bronze);
 table(10,21,2.4,1.0,1.5);chair(8.3,21);chair(11.7,21);for(const x of [15,18]){soft([x,1.08,20.5],[1.15,.25,2.2],linen);soft([x,1.45,19.6],[1.15,.75,.25],linen,[.35,0,0]);}
 for(let i=0;i<5;i++)box([36+i*1.6,.65-i*.11,13],[1.65,.18,3],stone);box([46,-.02,13],[8,.25,4],wood);
 for(let i=0;i<35;i++){const a=i*2.399;const x=Math.cos(a)*(49+3*Math.sin(i)),z=Math.sin(a)*(37+2*Math.cos(i));piece(sphere,stone,[x,.05,z],[1.8+(i%3),1.0+(i%4)*.25,1.5+(i%2)]);if(i%3===0){piece(sphere,foliage,[x*.85,1.0,z*.84],[1.8,.7,1.4]);}}
 for(const [x,z] of [[-26,-19],[25,-20],[-29,18],[33,20]]){piece(cylinder,wood,[x,2,z],[.10,3.4,.10]);for(let i=0;i<5;i++)piece(sphere,foliage,[x+Math.sin(i*2)*.5,3.7+Math.cos(i)*.3,z+Math.cos(i*2)*.5],[1,.7,.9]);}
 // Only a few material batches for hundreds of individually modelled details.
 for(const {g,m,matrices} of batches.values()){const mesh=new T.InstancedMesh(g,m,matrices.length);matrices.forEach((v,i)=>mesh.setMatrixAt(i,v));mesh.castShadow=m!==glass;mesh.receiveShadow=true;mesh.name='Residence material batch';mesh.computeBoundingSphere();root.add(mesh);}
 const number=createRoofNumber(root,10,10,6.52,5.5,20,17);
 // Metadata consumed by rain shielding; coordinates are in the shared plan units.
 for(const [x,z,w,d,h] of wings){const metadata=new T.Object3D();metadata.name='Residence dry room';metadata.userData={bounds:[(R.origin[0]+x-w/2)/S,(R.origin[0]+x+w/2)/S,(z-d/2)/S,(z+d/2)/S],floorY:R.floor/S,clearHeight:h+.3};scene.add(metadata);roofMetadata.push(metadata);}
 root.updateMatrixWorld(true);const point=new T.PointLight('#ffe0b2',160,28,2);point.position.set(8,4.8,4);root.add(point);const deskLight=new T.PointLight('#ffe0b2',100,18,2);deskLight.position.set(-12,3.7,-8);root.add(deskLight);
 return {root,update(camera,day){const close=camera.position.distanceTo(root.position)<180;point.visible=deskLight.visible=close;point.intensity=160*(1-.35*day);deskLight.intensity=100*(1-.35*day);light.emissiveIntensity=.3+(1-day)*.8;},dispose(){number.dispose();geometries.forEach(g=>g.dispose());textures.forEach(t=>t.dispose());owned.forEach(m=>m.dispose());roofMetadata.forEach(m=>scene.remove(m));scene.remove(root);}};
}
