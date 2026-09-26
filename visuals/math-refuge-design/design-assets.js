import * as T from 'three';
export const assetTypes={pavilion:'建筑 · 海上亭阁',library:'建筑 · 图书馆',classroom:'建筑 · 教学楼',tree:'树木',boat:'帆船',bench:'甲板长椅'};
export function createAsset(type,materials){
 const g=new T.Group();g.name=assetTypes[type];const wood=materials.timber,stone=materials.stone,steel=materials.steel;
 const add=(geo,mat,x,y,z)=>{const m=new T.Mesh(geo,mat);m.position.set(x,y,z);m.castShadow=m.receiveShadow=true;g.add(m);return m;};
 const box=(x,y,z,w,h,d,mat=wood)=>add(new T.BoxGeometry(w,h,d),mat,x,y,z);
 let w=24,d=18;
 if(['pavilion','library','classroom'].includes(type)){
  if(type==='classroom'){w=32;d=22;}box(0,-.2,0,w,1.2,d,stone);
  const floors=type==='classroom'?2:1;
  for(let f=0;f<floors;f++){const y=.4+f*4.5;box(0,y+4.2,0,w-2,.4,d-2,steel);for(const x of [-w/2+2,w/2-2])for(const z of [-d/2+2,0,d/2-2])box(x,y+2,z,.25,4,.25,wood);box(0,y,-1,w-4,.2,d-5,wood);box(0,y+2,-d/2+2,w-4,4,.2,materials.glass);
   if(type==='library')for(let x=-w/2+4;x<w/2-3;x+=3){box(x,y+1.3,-d/2+3,2.4,2.6,.6,wood);for(let i=0;i<3;i++)box(x,y+.5+i*.7,-d/2+2.65,2,.45,.15,materials.darkFabric);}
  }
 }else if(type==='tree'){w=d=4;add(new T.CylinderGeometry(.16,.3,4,10),wood,0,2,0);for(const [x,y,z,s]of [[0,5,0,1.8],[-1,4.2,.2,1.3],[1,4.6,-.3,1.5]]){const m=add(new T.IcosahedronGeometry(s,2),materials.leaf,x,y,z);m.scale.y=1.15;}}
 else if(type==='bench'){w=3;d=1;box(0,.65,0,3,.18,.85);box(0,1,-.4,3,.7,.13);for(const x of [-1.15,1.15])box(x,.3,0,.12,.6,.65,steel);}
 else {w=3;d=7;const hull=add(new T.SphereGeometry(1,16,8),wood,0,0,0);hull.scale.set(1.4,.6,3.5);box(0,3,0,.1,6,.1,steel);const geo=new T.BufferGeometry();geo.setAttribute('position',new T.Float32BufferAttribute([0,5.8,0,0,.8,0,0,.8,2.9],3));geo.computeVertexNormals();const sail=materials.pale.clone();sail.side=T.DoubleSide;add(geo,sail,0,0,0);}
 return {object:g,width:w,depth:d};
}
