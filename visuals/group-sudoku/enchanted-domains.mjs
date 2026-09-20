import * as T from '../3d/vendor/three.module.js';
import {masonryTexture} from './castle-materials.mjs?v=owls-low1';
import {hogwarts,whiteCity,icePalace,eyrie,movingKeep} from './castle-landmarks.mjs?v=owls-low1';
import {installIceSkaters} from './ice-skaters.mjs?v=skating1';
import {clockworkCity} from './clockwork.mjs?v=enchanted1';
import {jointMotion} from './architectural-motion.mjs?v=living1';
// Original miniature architecture: staged clockwork, luminous academies and glacial sculpture.
const material=(color,extra={})=>new T.MeshStandardMaterial({color,roughness:.65,...extra});
export function domainMaterials(a){
 if(a.enchantedMaterials)return a.enchantedMaterials;
 const stone=masonryTexture(),roof=masonryTexture(true);
 return a.enchantedMaterials={limestone:material(0xc5c5be,{map:stone,bumpMap:stone,bumpScale:.045}),slate:material(0x203f50,{map:roof,bumpMap:roof,bumpScale:.025,metalness:.18,roughness:.6}),snow:material(0xe1edf1),ice:material(0x89c7de,{metalness:.28,roughness:.16,emissive:0x123a58,emissiveIntensity:.25}),deepIce:material(0x316e90,{metalness:.4,roughness:.21}),window:material(0xffcf7c,{emissive:0xffa648,emissiveIntensity:.8,roughness:.3}),blue:material(0x99deeb,{emissive:0x4fadc7,emissiveIntensity:.45}),dark:material(0x152c3b),gold:a.materials.gold};
}
function group(parent,x=0,z=0){const g=new T.Group();g.position.set(x,.15,z);parent.add(g);return g;}
function arch(a,p,x,y,z,w,h,stone,light){
 const r=w/2,shape=new T.Shape();shape.moveTo(-r,0);shape.lineTo(-r,h-r);shape.quadraticCurveTo(-r,h-.1,0,h);shape.quadraticCurveTo(r,h-.1,r,h-r);shape.lineTo(r,0);shape.closePath();
 const pane=a.mesh(p,new T.ShapeGeometry(shape),light,[x,y,z]);pane.castShadow=false;
 const points=[[-r,0],[-r,h-r],[-r*.65,h-.15],[0,h],[r*.65,h-.15],[r,h-r],[r,0]].map(([px,py])=>new T.Vector3(x+px,y+py,z+.035));
 a.mesh(p,new T.TubeGeometry(new T.CatmullRomCurve3(points),18,.047,4,false),stone);a.rod(p,[x,y,z+.04],[x,y+h-.06,z+.04],.025,stone);a.rod(p,[x-r,y+h*.45,z+.04],[x+r,y+h*.45,z+.04],.021,stone);
}
function spire(a,p,x,z,h,r=.65){
 const M=domainMaterials(a),g=group(p,x,z);g.userData.landmark='academy-spire';a.cylinder(g,r*1.25,.22,[0,.1,0],M.limestone);a.cylinder(g,r,h,[0,h/2+.18,0],M.limestone);
 for(let y=.7;y<h;y+=1.1){a.torus(g,r+.015,.035,[0,y,0],a.materials.paper);for(const angle of [0,Math.PI/2,Math.PI,Math.PI*1.5]){const facade=group(g);facade.position.y=0;facade.rotation.y=angle;arch(a,facade,0,y-.23,r+.012,r*.48,.62,M.slate,M.window);}}
 a.cylinder(g,r*1.16,.18,[0,h+.22,0],M.limestone);a.mesh(g,new T.ConeGeometry(r*1.28,r*2.9,12),M.slate,[0,h+r*1.45+.31,0]);
 for(let j=1;j<=3;j++)a.torus(g,r*1.28*(1-j/4),.025,[0,h+.31+r*2.9*j/4,0],M.gold);
 a.rod(g,[0,h+r*2.9+.3,0],[0,h+r*2.9+.8,0],.024,M.gold);a.mesh(g,new T.OctahedronGeometry(.10),M.window,[0,h+r*2.9+.83,0]);return g;
}
function hall(a,p,x,z,w=5,h=2.6){
 const M=domainMaterials(a),g=group(p,x,z);g.userData.landmark='great-hall';a.box(g,[w+.35,.26,2.6],[0,.13,0],M.limestone);a.box(g,[w,h,2.25],[0,h/2+.25,0],M.limestone);
 for(let j=0;j<Math.floor(w/.85);j++){const xx=(j-(Math.floor(w/.85)-1)/2)*.86;arch(a,g,xx,.64,1.14,.46,h-1,M.slate,M.window);a.box(g,[.13,h+.12,.35],[xx+.35,h/2+.18,1.23],M.limestone);}
 for(const s of [-1,1]){const roof=a.box(g,[w+.55,.12,1.86],[0,h+.93,s*.65],M.slate);roof.rotation.x=s*.66;for(let j=0;j<7;j++)a.box(g,[w+.6,.032,.042],[0,h+1.46-j*.14,s*(.02+j*.21)],M.gold);}
 a.rod(g,[-w/2-.2,h+1.49,0],[w/2+.2,h+1.49,0],.05,M.gold);
 for(const xx of [-w*.34,w*.34]){a.box(g,[.3,1.3,.38],[xx,h+1.15,-.45],M.limestone);a.box(g,[.43,.1,.49],[xx,h+1.85,-.45],M.slate);}return g;
}
function viaduct(a,p,z,width=10){
 const M=domainMaterials(a),g=group(p,0,z);g.userData.landmark='arcaded-bridge';const bays=6,step=width/bays;
 for(let j=0;j<=bays;j++)a.box(g,[.3,1.85,.75],[-width/2+j*step,1.05,0],M.limestone);
 for(let j=0;j<bays;j++){const m=a.mesh(g,new T.TorusGeometry(step*.43,.13,5,18,Math.PI),M.limestone,[-width/2+(j+.5)*step,1.15,0]);m.rotation.z=0;}
 a.box(g,[width+.4,.24,1.15],[0,2.06,0],M.limestone);for(const zz of [-.52,.52]){a.box(g,[width+.4,.13,.14],[0,2.72,zz],M.limestone);for(let j=0;j<25;j++)a.box(g,[.075,.6,.075],[-width/2+j*width/24,2.4,zz],M.limestone);}return g;
}
function crystal(a,p,x,z,h=2,r=.55){const M=domainMaterials(a),g=group(p,x,z);g.userData.landmark='ice-crystal';a.cylinder(g,r*1.4,.16,[0,.08,0],M.snow);const m=a.mesh(g,new T.CylinderGeometry(r*.68,r,h*.65,6),M.ice,[0,h*.325+.15,0]);m.rotation.y=.2;a.mesh(g,new T.ConeGeometry(r*.68,h*.35,6),M.ice,[0,h*.825+.15,0]).rotation.y=.2;return g;}
function iceSwan(a,p,x,z,sign){const M=domainMaterials(a),g=group(p,x,z);g.userData.landmark='ice-swan';g.rotation.y=sign*.7;const body=a.mesh(g,new T.IcosahedronGeometry(.75,1),M.ice,[0,.65,0]);body.scale.set(.7,.66,1.3);const curve=new T.CatmullRomCurve3([new T.Vector3(0,.7,.45),new T.Vector3(0,1.3,.65),new T.Vector3(0,1.9,.65),new T.Vector3(0,2.15,1.0)]);a.mesh(g,new T.TubeGeometry(curve,20,.12,6,false),M.ice);a.mesh(g,new T.IcosahedronGeometry(.22,1),M.ice,[0,2.15,1]);const beak=a.mesh(g,new T.ConeGeometry(.12,.4,4),M.deepIce,[0,2.12,1.3]);beak.rotation.x=Math.PI/2;for(const s of [-1,1]){const wing=a.mesh(g,new T.ConeGeometry(.64,1.45,3),M.ice,[s*.46,1.1,-.17]);wing.scale.z=.25;wing.rotation.z=-s*.6;wing.rotation.x=-.35;}return g;}
function frostedPine(a,p,x,z,h){const M=domainMaterials(a);a.cylinder(p,.10,h*.6,[x,h*.3,z],a.materials.wood);for(let j=0;j<3;j++){const r=.8-j*.18,y=.9+j*.58;a.mesh(p,new T.ConeGeometry(r,h*.55,7),M.deepIce,[x,y,z]);a.mesh(p,new T.ConeGeometry(r*.94,h*.4,7),M.snow,[x,y+h*.11,z]);}}
function iceLake(a,p){
 const M=domainMaterials(a);p.userData.domain='glacial-lake';
 // Opaque reflective ice avoids transparent sorting and transmission render passes.
 a.cylinder(p,12.32,.12,[0,.17,0],M.deepIce);a.cylinder(p,12.08,.045,[0,.26,0],M.ice);a.torus(p,12.22,.16,[0,.28,0],M.snow);
 for(let k=0;k<24;k++){const q=k*Math.PI/12,r=7.5+(k%4)*.65;const x=Math.sin(q)*r,z=Math.cos(q)*r;a.line(p,[[x,.29,z],[x*.91+.22,.29,z*.91],[x*.79-.18,.29,z*.79]],0xd8f4ff,.4);}
 for(let k=0;k<11;k++){const q=-1.2+k*.24;const x=Math.sin(q)*11.25,z=-Math.cos(q)*11.25;crystal(a,p,x,z,1.4+(k%4)*.72,.44+(k%3)*.16);}
 for(const s of [-1,1]){iceSwan(a,p,s*10.35,-1.8,s);for(let j=0;j<3;j++)frostedPine(a,p,s*(10.3-j*.3),3+j*1.75,1.6+j*.15);}
 icePalace(a,p,castleKit(a));
 for(const s of [-1,1]){crystal(a,p,s*3,10.5,1.25,.38);a.torus(p,.65,.08,[s*3,.31,10.5],M.snow);}
 installIceSkaters(a,p);
}
function castleKit(a){return {M:domainMaterials(a),group,arch,spire,hall,viaduct};}
export function replaceDomain(a,p,index){if(index===4){clockworkCity(a,p);movingKeep(a,p,castleKit(a));return true;}if(index===2){iceLake(a,p);return true;}if(index===3){whiteCity(a,p,castleKit(a));return true;}if(index===5){eyrie(a,p,castleKit(a));return true;}if(index===6){hogwarts(a,p,castleKit(a));return true;}return false;}
export function enrichDomain(a,p,index){
 const M=domainMaterials(a);p.userData.domain??=['clockwork-garden','jade-pavilion','glacial-lake','rose-chapel','brass-city','astral-sanctuary','enchanted-academy','celestial-wall'][index];
 // Terraced stone approaches, inset path and edge lighting tie the miniature together.
 for(const side of [-1,1])for(let j=0;j<4;j++)a.box(p,[1.6,.12+j*.08,.40],[side*3.8,.17+j*.04,8.9-j*.37],index===2?M.snow:a.materials.stone);
 if(index===0){for(const s of [-1,1]){spire(a,p,s*3.2,-8.6,2.3,.42);}const dial=group(p,0,-9.3);a.gear(dial,1.2,28,[0,.4,0],.10);a.torus(dial,1.38,.055,[0,.5,0],M.gold);}
 if(index===1){for(const s of [-1,1])for(let j=0;j<3;j++){const z=-1+j*2;a.cylinder(p,.05,1.2,[s*7.6,.77,z],M.gold);a.mesh(p,new T.SphereGeometry(.16,8,6),M.window,[s*7.6,1.4,z]);}for(let j=0;j<5;j++)a.box(p,[3.4-j*.28,.1,.45],[0,.18+j*.07,-6.25-j*.36],a.materials.stone);}


 if(index===7){for(const s of [-1,1]){const beacon=group(p,s*10,4.1);a.cylinder(beacon,.36,1.4,[0,.85,0],a.materials.stone);a.cylinder(beacon,.55,.18,[0,1.62,0],M.gold);const flame=a.mesh(beacon,new T.OctahedronGeometry(.3),M.window,[0,1.99,0]);flame.scale.y=1.7;}}
}
