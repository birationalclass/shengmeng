import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=living1';
const mat=(color,extra={})=>new T.MeshStandardMaterial({color,roughness:.7,...extra});
function label(a,p,text,width,height,pos,color='#d6b56a'){
 if(typeof document==='undefined')return;
 const canvas=document.createElement('canvas');canvas.width=1024;canvas.height=256;const c=canvas.getContext('2d');c.fillStyle=color;c.textAlign='center';c.textBaseline='middle';c.font='600 148px "Songti SC","Noto Serif SC",serif';c.fillText(text,512,132,960);
 const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;const m=new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,side:T.DoubleSide});return a.mesh(p,new T.PlaneGeometry(width,height),m,pos);
}
export function ecnuCampus(a,p){
 p.userData.domain='ecnu-mathematics';
 const stone=mat(0xc6c9c2),metal=mat(0x708889,{metalness:.68,roughness:.35}),glass=mat(0x638895,{metalness:.5,roughness:.22}),roof=mat(0x687879),green=mat(0x53764d),pink=mat(0xe5c6cf),wood=a.materials.wood;
 const panes=[0x668995,0x628692,0x6a8e99,0x648995].map(c=>mat(c,{metalness:.42,roughness:.25}));
 // Curved blue-green curtain wall and the cylindrical glazed volume in the
 // School's official photographs. Proportions are adapted to the board perimeter.
 function glazedRound(x,z,r,h,depth=1){const g=new T.Group();g.position.set(x,.16,z);p.add(g);g.userData.landmark='ecnu-curtain-wall';
  a.cylinder(g,r+.14,.16,[0,.10,0],stone).scale.z=depth;
  const drum=a.cylinder(g,r,h,[0,h/2+.20,0],glass);drum.scale.z=depth;
  const floors=Math.round(h/.62),bays=40;
  for(let j=0;j<=floors;j++){const ring=a.torus(g,r+.022,.034,[0,.24+j*(h/floors),0],metal);ring.scale.y=depth;}
  for(let k=0;k<bays;k++){const q=k*Math.PI*2/bays,xx=Math.sin(q)*r,zz=Math.cos(q)*r*depth;a.rod(g,[xx,.2,zz],[xx,h+.34,zz],.032,metal);
   for(let row=0;row<floors;row++){const q2=q+Math.PI/bays,w=2*r*Math.sin(Math.PI/bays)*.92,window=a.box(g,[w,h/floors-.09,.028],[Math.sin(q2)*(r+.025),.24+(row+.5)*h/floors,Math.cos(q2)*(r+.025)*depth],panes[(k+row*3)%panes.length]);window.rotation.y=Math.atan2(Math.sin(q2)*depth,Math.cos(q2));window.scale.x=Math.hypot(Math.cos(q2),Math.sin(q2)*depth);}
  }
  a.cylinder(g,r+.12,.12,[0,h+.3,0],roof).scale.z=depth;
  a.box(g,[r*.65,.22,r*.4],[0,h+.43,0],metal);for(let j=0;j<5;j++)a.box(g,[r*.56,.025,.028],[0,h+.55,(j-2)*r*.065],roof);
  for(let k=0;k<32;k++){const q=k*Math.PI/16;a.rod(g,[Math.sin(q)*r,h+.36,Math.cos(q)*r*depth],[Math.sin(q)*r,h+.65,Math.cos(q)*r*depth],.023,metal);}a.torus(g,r,.025,[0,h+.66,0],metal).scale.y=depth;return g;
 }
 const main=glazedRound(-.25,-9.0,3.62,4.25,.58);glazedRound(-7.8,-7.0,1.64,6.5,1);
 // White-clad rectangular teaching wing, horizontal window ribbons and louvers.
 const wing=new T.Group();wing.position.set(8.0,.15,-3.6);p.add(wing);wing.userData.landmark='ecnu-teaching-wing';
 a.box(wing,[2.7,3.9,8.0],[0,2.05,0],stone);a.box(wing,[2.98,.16,8.25],[0,4.1,0],roof);
 for(let floor=0;floor<4;floor++){const y=.65+floor*.84;for(let j=0;j<10;j++)for(const side of [-1,1]){a.box(wing,[.035,.55,.55],[side*1.365,y,-3.53+j*.78],panes[(j+floor)%4]);}for(let j=0;j<3;j++)a.box(wing,[.52,.55,.035],[-.85+j*.85,y,4.015],glass);a.box(wing,[2.72,.065,8.03],[0,y+.36,0],metal);}
 for(const x of [-.8,.8])for(let j=0;j<8;j++)a.box(wing,[.48,.05,.055],[x,3.32+j*.06,4.05],metal);
 // Raised glass link, supported on a clear ground-floor passage.
 a.box(p,[4.8,.18,1.14],[5.15,2.0,-8.3],stone);a.box(p,[4.8,1.16,.055],[5.15,2.68,-7.75],glass);a.box(p,[4.8,1.16,.055],[5.15,2.68,-8.84],glass);a.box(p,[4.96,.12,1.3],[5.15,3.3,-8.3],roof);
 for(let k=0;k<10;k++)for(const zz of [-7.72,-8.87])a.box(p,[.045,1.15,.045],[2.95+k*.49,2.68,zz],metal);
 for(const x of [4.1,6.7])a.cylinder(p,.14,1.95,[x,1.03,-8.3],stone);
 // Entrance canopy, gold building name and glazed double doors.
 a.box(p,[2.5,.09,.92],[-.25,1.52,-6.55],glass);for(const x of [-1.32,.82])a.cylinder(p,.038,1.4,[x,.83,-6.18],metal);
 for(const x of [-.67,.17]){a.box(p,[.75,1.2,.055],[x,.82,-6.87],panes[2]);a.box(p,[.035,.36,.05],[x+.25,.9,-6.82],metal);}
 label(a,p,'数学楼',2.65,.65,[-.25,2.95,-6.82]);
 for(let j=0;j<3;j++)a.box(p,[2.75,.07,.21],[-.25,.12+j*.065,-6.02-j*.23],stone);
 // A cherry-lined campus walk and simple benches replace fantasy spires.
 for(const side of [-1,1]){a.box(p,[1.4,.08,7.0],[side*8.1,.16,4.0],stone);for(const z of [1.5,5.5]){
   const x=side*9.6;a.cylinder(p,.66,.16,[x,.20,z],stone);a.cylinder(p,.12,1.85,[x,1.14,z],wood);
   const crown=new T.Group();crown.position.set(x,2.3,z);p.add(crown);for(let k=0;k<9;k++){const q=k*2.4,leaf=a.mesh(crown,new T.IcosahedronGeometry(.46,1),pink,[Math.sin(q)*.62,(k%3)*.18,Math.cos(q)*.62]);leaf.scale.y=.65;}jointMotion(a,crown,{axis:'z',amplitude:.035,speed:.45,phase:z});
   a.box(p,[.62,.13,1.6],[side*7.2,.61,z],wood);for(const zz of [-.55,.55])a.box(p,[.42,.43,.1],[side*7.2,.33,z+zz],metal);
  }
  for(let j=0;j<6;j++)a.mesh(p,new T.IcosahedronGeometry(.35,1),green,[side*10.45,.43,1+j*.94]);
 }
 // Official seal is used intact on an ivory medallion, not behind the cells.
 const medal=a.cylinder(p,2.05,.13,[0,.20,9.4],stone);medal.userData.landmark='ecnu-official-seal';a.torus(p,2.06,.035,[0,.29,9.4],mat(0x93c4dc,{metalness:.18,roughness:.5}));
 if(typeof document!=='undefined'){
  const texture=new T.TextureLoader().load(new URL('./images/ecnu-seal.png',import.meta.url).href,t=>{const canvas=document.createElement('canvas');canvas.width=768;canvas.height=779;const ctx=canvas.getContext('2d');ctx.drawImage(t.image,0,0,768,779);const pixels=ctx.getImageData(0,0,768,779),d=pixels.data;for(let i=0;i<d.length;i+=4){const ink=Math.min(1,(255-d[i+1])/224);d[i]=147;d[i+1]=196;d[i+2]=220;d[i+3]=Math.round(d[i+3]*ink);}ctx.putImageData(pixels,0,0);t.image=canvas;t.needsUpdate=true;});texture.colorSpace=T.SRGBColorSpace;
  const image=a.mesh(p,new T.PlaneGeometry(3.76*5907/5988,3.76),new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false}),[0,.28,9.4]);image.rotation.x=-Math.PI/2;
 }
 label(a,p,'华东师范大学',3.8,.44,[0,.7,11.6],'#7d3448');
 return p;
}
