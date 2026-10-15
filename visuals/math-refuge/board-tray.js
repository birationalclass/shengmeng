import {TRAY_WOOD_DATA} from './board-tray-grain.js';
import {TRAY_DOCK} from './board-tray-layout.js';
import {TRAY} from './board-hardware.js';
// Shared geometry and deterministic small PBR maps: no image downloads or extra
// work during narration. End faces have their own grain direction, not a butt cap.
export function createBoardTrayHardware(T,anisotropy=1){
 const maps=[],materials=[],geometries=[],woodGeometries=[];let tone='deep';
 const width=1024,height=256,color=new Uint8Array(width*height*4),bump=new Uint8Array(color.length);
 for(let y=0;y<height;y++)for(let x=0;x<width;x++){
  const u=x/width,v=y/height,warp=v*65+1.2*Math.sin(u*8+v*3)+.35*Math.sin(u*27+v*8),vein=Math.sin(warp*6.283),fine=Math.sin(warp*19.8+u*6),noise=(((x*73+y*151+x*y*7)%131)/131-.5);
  const light=1+vein*.043+fine*.018+noise*.025,i=(y*width+x)*4;
  color.set([Math.round(151*light),Math.round(116*light),Math.round(76*light),255],i);
  const n=Math.round(128+vein*17+fine*7+noise*7);bump.set([n,n,n,255],i);
 }
 function texture(bytes,srgb=false){const map=new T.DataTexture(bytes,width,height);if(srgb)map.colorSpace=T.SRGBColorSpace;map.wrapS=map.wrapT=T.RepeatWrapping;map.generateMipmaps=true;map.minFilter=T.LinearMipmapLinearFilter;map.anisotropy=Math.min(8,anisotropy);map.needsUpdate=true;maps.push(map);return map;}
 const grain=texture(color,true),relief=texture(bump),wood=new T.MeshPhysicalMaterial({color:'#646464',vertexColors:true,map:grain,bumpMap:relief,bumpScale:.0004,roughness:.63,metalness:0,clearcoat:.06,clearcoatRoughness:.65,envMapIntensity:.25});
 wood.name='Satin nanmu with longitudinal fine grain';materials.push(wood);
 function tintGeometry(g,bottom,top){
  const p=g.getAttribute('position'),attribute=g.getAttribute('color')||new T.BufferAttribute(new Float32Array(p.count*3),3),a=new T.Color(tone==='gradient'?'#414c4b':'#ffffff'),b=new T.Color(tone==='gradient'?'#98836d':'#ffffff'),c=new T.Color();
  for(let i=0;i<p.count;i++){const t=Math.max(0,Math.min(1,(p.getY(i)-bottom)/(top-bottom)));c.copy(a).lerp(b,t*t*(3-2*t));c.toArray(attribute.array,i*3);}g.setAttribute('color',attribute);attribute.needsUpdate=true;
 }
 function woodGeometry(g,bottom,top){woodGeometries.push({g,bottom,top});tintGeometry(g,bottom,top);return g;}
 function setTone(value){tone=['deep','honey','gradient'].includes(value)?value:'deep';wood.color.set(tone==='deep'?'#646464':tone==='honey'?'#8c7963':'#ffffff');woodGeometries.forEach(({g,bottom,top})=>tintGeometry(g,bottom,top));return tone;}
 const glass=new T.MeshPhysicalMaterial({color:'#0c1714',roughness:.86,metalness:0,clearcoat:0,specularIntensity:0,envMapIntensity:0});glass.name='Flush low-reflection touch glass';materials.push(glass);
 const steel=new T.MeshStandardMaterial({color:'#454a45',roughness:.58,metalness:.52,envMapIntensity:.15});materials.push(steel);
 function roundedProfile(points,radius){const shape=new T.Shape(),count=points.length;for(let i=0;i<count;i++){
  const p=points[i],prev=points[(i+count-1)%count],next=points[(i+1)%count],a=Math.hypot(prev[0]-p[0],prev[1]-p[1]),b=Math.hypot(next[0]-p[0],next[1]-p[1]),r=Math.min(radius,a*.35,b*.35),from=[p[0]+(prev[0]-p[0])*r/a,p[1]+(prev[1]-p[1])*r/a],to=[p[0]+(next[0]-p[0])*r/b,p[1]+(next[1]-p[1])*r/b];
  if(i===0)shape.moveTo(...from);else shape.lineTo(...from);shape.quadraticCurveTo(...p,...to);
 }shape.closePath();return shape;}
 // Shape coordinates are (-z,y); extrusion is rotated onto the board's x axis.
 const profile=roundedProfile([[-.33,.585],[.23,.615],[.23,.735],[.18,.735],[.18,.655],[-.06,.655],[-.06,.71],[-.24,.71],[-.32,.59]],.007);
 const body=new T.ExtrudeGeometry(profile,{depth:TRAY_DOCK.width-.024,bevelEnabled:true,bevelSize:.005,bevelThickness:.012,bevelSegments:3,steps:1,curveSegments:5});body.rotateY(Math.PI/2);body.translate(-(TRAY_DOCK.width-.024)/2,0,TRAY.z);
 woodGeometry(body,.58,.74);const positions=body.getAttribute('position'),normals=body.getAttribute('normal'),uv=body.getAttribute('uv');
 for(let i=0;i<positions.count;i++){const x=positions.getX(i),y=positions.getY(i),z=positions.getZ(i);uv.setXY(i,Math.abs(normals.getX(i))>.8?(z-TRAY.z+.24)/.58:x/TRAY_DOCK.width+.5,(Math.abs(normals.getX(i))>.8?(y-.57)/.18:(z-TRAY.z)*1.2+y*.14+.3));}uv.needsUpdate=true;geometries.push(body);
 function roundedSlab(w,h,d,r){const shape=roundedProfile([[-w/2,-h/2],[w/2,-h/2],[w/2,h/2],[-w/2,h/2]],r),g=new T.ExtrudeGeometry(shape,{depth:d-.004,bevelEnabled:true,bevelSize:.002,bevelThickness:.002,bevelSegments:2,curveSegments:5,steps:1});g.translate(0,0,-d/2+.002);geometries.push(g);return g;}
 const panel=roundedSlab(TRAY_DOCK.panelWidth,TRAY_DOCK.panelHeight,.014,.028),bracket=new T.BoxGeometry(.055,.10,.26);geometries.push(bracket);
 const frames=new Map();
 function frameRails(w,h){
  const key=w+':'+h;if(frames.has(key))return frames.get(key);
  const ox=w/2+.040,oy=h/2+.040,ix=w/2+.008,iy=h/2+.008;
  const outlines=[[[ -ox,oy],[ -ix,iy],[ix,iy],[ox,oy]],[[ -ox,-oy],[ox,-oy],[ix,-iy],[-ix,-iy]],[[ -ox,-oy],[-ix,-iy],[-ix,iy],[-ox,oy]],[[ox,-oy],[ox,oy],[ix,iy],[ix,-iy]]];
  const rails=outlines.map((points,index)=>{const shape=new T.Shape();shape.moveTo(...points[0]);points.slice(1).forEach(p=>shape.lineTo(...p));shape.closePath();const g=new T.ExtrudeGeometry(shape,{depth:.066,bevelEnabled:true,bevelSize:.0025,bevelThickness:.0025,bevelSegments:3,steps:1});g.translate(0,0,-.055);const p=g.getAttribute('position'),uv=g.getAttribute('uv');for(let i=0;i<p.count;i++){const x=p.getX(i),y=p.getY(i);uv.setXY(i,index<2?x/w+.5:y/h+.5,index<2?(y+(index?oy:-iy))/.08+.2:(x+(index===2?ox:-ix))/.08+.45);}uv.needsUpdate=true;geometries.push(g);woodGeometry(g,-oy,oy);return g;});frames.set(key,rails);return rails;
 }
 return {setTone,get tone(){return tone;},createFrame(parent,w,h){const frame=new T.Group();frame.name='Fine mitered nanmu board frame';parent.add(frame);frameRails(w,h).forEach((g,i)=>{const rail=new T.Mesh(g,wood);rail.name=['Top','Bottom','Left','Right'][i]+' beveled mitered wood rail';rail.castShadow=true;rail.receiveShadow=true;frame.add(rail);});return frame;},async loadGrain(){const map=await new T.TextureLoader().loadAsync(TRAY_WOOD_DATA);map.colorSpace=T.SRGBColorSpace;map.wrapS=map.wrapT=T.RepeatWrapping;map.anisotropy=Math.min(8,anisotropy);for(const old of maps)old.dispose();maps.length=0;maps.push(map);wood.map=map;wood.bumpMap=map;wood.bumpScale=.0008;setTone(tone);wood.needsUpdate=true;},create(parent,cx,column){
  const group=new T.Group();group.name='Wide nanmu chalk tray '+(column+1);group.position.x=cx;group.userData={column,depth:.61,centerZ:TRAY.z,floorTop:TRAY.top,integratedControls:true};parent.add(group);
  const shell=new T.Mesh(body,wood);shell.name='Continuous rounded gutter and chamfered control shoulder';shell.castShadow=true;shell.receiveShadow=true;group.add(shell);
  const strip=new T.Mesh(panel,glass);strip.position.set(0,TRAY_DOCK.y,TRAY_DOCK.z);strip.rotation.x=-TRAY_DOCK.tilt;strip.name='Recessed matte glass control strip';strip.receiveShadow=true;group.add(strip);
  for(const x of [-1.90,1.90]){const support=new T.Mesh(bracket,steel);support.position.set(x,.56,TRAY.z-.05);support.name='Discreet tray support';group.add(support);}
  return group;
 },dispose(){maps.forEach(m=>m.dispose());materials.forEach(m=>m.dispose());geometries.forEach(g=>g.dispose());}};
}
