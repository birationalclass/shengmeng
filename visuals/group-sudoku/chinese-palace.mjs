import {installPalaceFountains} from './palace-fountains.mjs?v=palace-water1';
import * as T from '../3d/vendor/three.module.js';
import {jointMotion} from './architectural-motion.mjs?v=wizard1';
const material=(color,metalness=.05)=>new T.MeshStandardMaterial({color,roughness:.61,metalness});
// Palace Museum roof/terrace vocabulary and the Temple of Heaven's triple circular eaves.
// A miniature composition, rather than a geographic reconstruction of either complex.
export function chinesePalace(a,p){
 p.userData.domain='chinese-palace-garden';
 const M={red:material(0x86352d),gold:material(0xcba654,.25),tile:material(0xb58b39,.22),blue:material(0x285d7a,.22),jade:material(0x427366),white:material(0xd7d7c8),stone:material(0x929887),dark:material(0x273c37),green:material(0x3d624b),wood:material(0x633c29)};
 const group=(parent,x,y,z,name)=>{const g=new T.Group();g.position.set(x,y,z);g.userData.landmark=name;parent.add(g);return g;};
 const rod=(g,x,y,r=.025,m=M.gold)=>a.rod(g,x,y,r,m);
 function rail(g,w,d,y){for(const z of [-d/2,d/2]){rod(g,[-w/2,y+.36,z],[w/2,y+.36,z],.035,M.white);for(let k=0;k<=Math.ceil(w/.55);k++){const x=-w/2+k*w/Math.ceil(w/.55);a.cylinder(g,.037,.43,[x,y+.22,z],M.white);a.mesh(g,new T.SphereGeometry(.065,6,4),M.white,[x,y+.45,z]);}}for(const x of [-w/2,w/2]){rod(g,[x,y+.36,-d/2],[x,y+.36,d/2],.035,M.white);for(let z=-d/2;z<=d/2;z+=.5)a.cylinder(g,.035,.42,[x,y+.21,z],M.white);}}
 function terrace(g,w,d,levels=2){for(let k=0;k<levels;k++)a.box(g,[w-k*.28,.18,d-k*.24],[0,.09+k*.18,0],M.white);rail(g,w-.2,d-.2,levels*.18);}
 // Four curved roof faces meet along a ridge; outward corners curl upward.
 function roof(g,w,d,y,h,m=M.tile){
 const pos=[],uv=[];const ridge=Math.max(0,(w-d)*.39),sides=[[[w/2,d/2],[-w/2,d/2],[ridge,0],[-ridge,0]], [[-w/2,-d/2],[w/2,-d/2],[-ridge,0],[ridge,0]], [[w/2,-d/2],[w/2,d/2],[ridge,0],[ridge,0]], [[-w/2,d/2],[-w/2,-d/2],[-ridge,0],[-ridge,0]]];
 const sample=(s,u,v)=>{const [A,B,C,D]=s;return [(C[0]*(1-v)+D[0]*v)*(1-u)+(A[0]*(1-v)+B[0]*v)*u,y+h*Math.pow(1-u,1.8)+.19*Math.pow(u,7)*Math.pow(Math.abs(v*2-1),5),(C[1]*(1-v)+D[1]*v)*(1-u)+(A[1]*(1-v)+B[1]*v)*u];};
 for(const s of sides){for(let i=0;i<8;i++)for(let j=0;j<16;j++){const pts=[sample(s,i/8,j/16),sample(s,(i+1)/8,j/16),sample(s,(i+1)/8,(j+1)/16),sample(s,i/8,(j+1)/16)];for(const k of [0,1,2,0,2,3])pos.push(...pts[k]);}for(let j=0;j<=16;j++){const points=Array.from({length:9},(_,k)=>new T.Vector3(...sample(s,k/8,j/16)));a.mesh(g,new T.TubeGeometry(new T.CatmullRomCurve3(points),8,.018,4,false),M.gold);}const edge=Array.from({length:17},(_,j)=>new T.Vector3(...sample(s,1,j/16)));a.mesh(g,new T.TubeGeometry(new T.CatmullRomCurve3(edge),16,.038,5,false),M.gold);}
 const geo=new T.BufferGeometry();geo.setAttribute('position',new T.Float32BufferAttribute(pos,3));geo.computeVertexNormals();const roofMaterial=m.clone();roofMaterial.side=T.DoubleSide;a.mesh(g,geo,roofMaterial);rod(g,[-ridge-.13,y+h+.055,0],[ridge+.13,y+h+.055,0],.055);for(const side of [-1,1]){a.mesh(g,new T.ConeGeometry(.12,.30,5),M.gold,[side*(ridge+.10),y+h+.18,0]).rotation.z=-side*.35;}
 }
 function lantern(g,x,y,z,phase){const q=group(g,x,y,z,'hanging-palace-lantern');rod(q,[0,0,0],[0,-.17,0],.018);a.mesh(q,new T.SphereGeometry(.115,8,6),M.red,[0,-.28,0]).scale.y=1.22;a.cylinder(q,.09,.035,[0,-.15,0],M.gold);rod(q,[0,-.41,0],[0,-.56,0],.014);jointMotion(a,q,{axis:'z',amplitude:.12,speed:1.1,phase});}
 function hall(x,z,w,d,h,name,double=true,color=M.tile){const g=group(p,x,.18,z,name);terrace(g,w+.8,d+.7,3);a.box(g,[w*.9,h,d*.7],[0,.54+h/2,0],M.red);a.box(g,[w+.15,.13,d+.06],[0,.61+h,0],M.jade);
 for(const side of [-1,1])for(let j=0;j<=6;j++){const xx=-w*.45+j*w*.9/6;a.cylinder(g,.065,h,[xx,.54+h/2,side*d*.44],M.red);a.box(g,[.25,.12,.28],[xx,.59+h,side*d*.44],M.gold);a.box(g,[.33,.08,.32],[xx,.70+h,side*d*.44],M.jade);if(j<6){const cx=xx+w*.075;a.box(g,[w*.13,h*.68,.055],[cx,.64+h*.44,side*(d*.355)],M.dark);for(let k=0;k<3;k++)a.box(g,[.019,h*.64,.028],[cx+(k-1)*w*.035,.64+h*.44,side*(d*.39)],M.gold);}}
 roof(g,w+.75,d+.70,h+.73,double?.55:.70,color);if(double){a.box(g,[w*.70,.58,d*.57],[0,h+1.04,0],M.red);roof(g,w*.9,d*.91,h+1.34,.8,color);}
 for(let j=0;j<5;j++)a.box(g,[w*.25,.11,.26],[0,.055+j*.11,d/2+.83-j*.19],M.white);for(const s of [-1,1])lantern(g,s*w*.33,h+.60,d*.48,x+s);return g;}
 function roundTemple(x,z,r=1.75){const g=group(p,x,.18,z,'temple-of-heaven-inspired');for(let k=0;k<3;k++){const rr=r+.42-k*.16;a.cylinder(g,rr,.19,[0,.095+k*.19,0],M.white);for(let j=0;j<24;j++){const q=j*Math.PI/12;a.cylinder(g,.028,.28,[Math.sin(q)*(rr-.10),.34+k*.19,Math.cos(q)*(rr-.10)],M.white);}a.torus(g,rr-.10,.025,[0,.47+k*.19,0],M.white);}
 for(let tier=0;tier<3;tier++){const radius=r*(1-tier*.21),y=.60+tier*.93;a.cylinder(g,radius*.76,.85,[0,y+.42,0],M.red);for(let j=0;j<16;j++){const q=j*Math.PI/8;a.cylinder(g,.044,.78,[Math.sin(q)*radius*.80,y+.39,Math.cos(q)*radius*.80],M.red);}a.torus(g,radius*.82,.06,[0,y+.68,0],M.jade);const profile=[[0,.64],[radius*.22,.58],[radius*.52,.30],[radius*.80,.065],[radius,0],[radius*1.045,.06]].map(([xx,yy])=>new T.Vector2(xx,yy));a.mesh(g,new T.LatheGeometry([...profile].reverse(),48),M.blue,[0,y+.82,0]);a.torus(g,radius,.035,[0,y+.82,0],M.gold);for(let j=0;j<32;j++){const q=j*Math.PI/16;const pts=profile.slice(1).map(v=>new T.Vector3(Math.sin(q)*v.x,y+.83+v.y,Math.cos(q)*v.x));a.mesh(g,new T.TubeGeometry(new T.CatmullRomCurve3(pts),8,.012,3,false),M.gold);}}
 a.mesh(g,new T.SphereGeometry(.14,10,8),M.gold,[0,4.10,0]);a.mesh(g,new T.ConeGeometry(.08,.28,8),M.gold,[0,4.30,0]);return g;}
 function pavilion(x,z,scale=1,name='garden-pavilion'){const g=group(p,x,.18,z,name);g.scale.setScalar(scale);terrace(g,2.3,2.3,2);for(const xx of [-.76,.76])for(const zz of [-.76,.76])a.cylinder(g,.065,1.65,[xx,1.17,zz],M.red);roof(g,2.7,2.7,2,.78,M.jade);for(const side of [-1,1]){a.box(g,[1.50,.12,.25],[0,.68,side*.76],M.red);lantern(g,side*.72,1.9,.75,x+side);}return g;}
 function corridor(side){const g=group(p,side*10.45,.18,1.55,'covered-palace-gallery');a.box(g,[1.55,.22,4],[0,.11,0],M.white);for(const x of [-.54,.54])for(let k=0;k<6;k++)a.cylinder(g,.045,1.36,[x,.89,-1.8+k*.72],M.red);const top=group(g,0,0,0);top.rotation.y=Math.PI/2;roof(top,4.5,1.80,1.59,.45,M.jade);for(const s of [-1,1])lantern(g,s*.51,1.46,1.7,side+s);}
 // The themed paving covers the full usable disk after assembly, including its outer rim.
 const paving=M.stone.clone();
 if(typeof document!=='undefined'){
  const canvas=document.createElement('canvas');canvas.width=canvas.height=1536;const ctx=canvas.getContext('2d');ctx.fillStyle='#a9ae9e';ctx.fillRect(0,0,1536,1536);
  const step=48;for(let row=0;row<33;row++)for(let col=-1;col<33;col++){const x=col*step+(row%2)*step/2,y=row*step,v=158+((row*13+col*7+256)%12);ctx.fillStyle=`rgb(${v+6},${v+9},${v-3})`;ctx.fillRect(x+1,y+1,step-2,step-2);ctx.strokeStyle='#d1d2bd';ctx.lineWidth=1;ctx.strokeRect(x+2,y+2,step-4,step-4);}
  for(const [radius,width,color]of [[751,24,'#c6c6b0'],[731,3,'#7a8c7f'],[715,2,'#cfcdad']]){ctx.beginPath();ctx.arc(768,768,radius,0,Math.PI*2);ctx.lineWidth=width;ctx.strokeStyle=color;ctx.stroke();}
  const map=new T.CanvasTexture(canvas);map.colorSpace=T.SRGBColorSpace;paving.map=map;
 }
 a.cylinder(p,12.73,.10,[0,.20,0],M.stone);const pavedDisk=a.mesh(p,new T.CircleGeometry(12.73,128),paving,[0,.256,0]);pavedDisk.rotation.x=-Math.PI/2;pavedDisk.userData.landmark='full-palace-paving';a.torus(p,12.72,.045,[0,.28,0],M.white);
 installPalaceFountains(a,p);
 // Taller silhouettes at the back; small pavilions and open space in front.
 hall(0,-9.1,6.4,2.65,1.72,'imperial-double-eaved-hall',true);
 hall(-6.8,-8.1,2.4,1.85,1.50,'western-palace-tower',true);hall(6.8,-8.1,2.4,1.85,1.95,'eastern-palace-tower',true);
 roundTemple(-9.25,-2.8,1.65);
 const pagoda=group(p,9.1,.18,-3.1,'five-storey-garden-pagoda');for(let k=0;k<5;k++){const w=2.15-k*.22,y=k*.82;a.box(pagoda,[w*.70,.65,w*.70],[0,y+.43,0],M.red);roof(pagoda,w,w,y+.78,.43,k%2?M.jade:M.tile);for(const s of [-1,1])a.box(pagoda,[.24,.35,.025],[0,y+.42,s*w*.355],M.dark);}a.mesh(pagoda,new T.ConeGeometry(.08,.35,6),M.gold,[0,4.62,0]);
 corridor(-1);corridor(1);
 hall(-8.25,5.55,2.05,1.65,1.0,'western-study-hall',false,M.jade);hall(8.25,5.55,2.05,1.65,1.25,'eastern-study-hall',false,M.tile);
 pavilion(-4.8,9.0,.85,'western-lakeside-pavilion');pavilion(4.8,9.0,.95,'eastern-lakeside-pavilion');
 const gate=group(p,0,.18,10.25,'ceremonial-paifang');for(const x of [-1.75,-.75,.75,1.75]){a.box(gate,[.3,.16,.38],[x,.10,0],M.white);a.cylinder(gate,.075,x===-.75||x===.75?1.8:1.4,[x,x===-.75||x===.75?.98:.78,0],M.red);}a.box(gate,[3.8,.22,.25],[0,1.45,0],M.jade);roof(gate,2.15,.85,1.91,.36,M.tile);for(const s of [-1,1]){const wing=group(gate,s*1.39,0,0);roof(wing,1.10,.8,1.53,.28,M.tile);}a.box(gate,[.7,.27,.05],[0,1.70,.15],M.blue);
 for(const side of [-1,1])for(const z of [3.8,7.1]){const x=side*(z>5?6.9:8.2);const tree=group(p,x,.2,z,'palace-cypress');a.cylinder(tree,.07,1.30,[0,.65,0],M.wood);for(let k=0;k<3;k++)a.mesh(tree,new T.IcosahedronGeometry(.40-k*.06,1),M.green,[0,1.0+k*.36,0]).scale.set(.85,1.35,.85);}
}
