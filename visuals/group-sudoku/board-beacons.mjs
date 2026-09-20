import * as T from '../3d/vendor/three.module.js';
export function beaconProgress(values){const filled=values.filter(v=>Number.isInteger(v)&&v>=1&&v<=9).length;return {filled,total:81,wallLit:Math.floor(filled*8/81)};}
export function installWallBeacon(a,tower,height,index){
 const root=new T.Group();root.position.set(0,height,0);root.userData.landmark='wall-brazier';tower.add(root);
 a.cylinder(root,.34,.18,[0,.09,0],a.materials.dark);
 for(const x of [-.27,.27])for(const z of [-.27,.27])a.box(root,[.07,.27,.07],[x,.22,z],a.materials.brass);
 const fire=new T.Group();root.add(fire);fire.position.y=.18;fire.visible=false;
 const outer=new T.Mesh(new T.ConeGeometry(.27,.90,7),new T.MeshBasicMaterial({color:0xff8d25}));outer.position.y=.45;
 const inner=new T.Mesh(new T.ConeGeometry(.15,.65,7),new T.MeshBasicMaterial({color:0xffdc70}));inner.position.set(.025,.33,.04);fire.add(outer,inner);
 const embers=Array.from({length:4},()=>{const mesh=new T.Mesh(new T.SphereGeometry(.025,4,3),new T.MeshBasicMaterial({color:0xffc85b}));fire.add(mesh);return mesh;});
 const beacon={root,fire,embers,index,active:false,ignition:0};a.wallBeacons.push(beacon);return beacon;
}
export function syncWallBeacons(wall=[],values=[]){const state=beaconProgress(values);wall.forEach((p,i)=>{const active=i<state.wallLit;if(active&&!p.active)p.ignition=0;p.active=active;p.fire.visible=active;if(!active)p.ignition=0;});return state;}
export function updateWallBeacons(wall=[],time,dt,reduced=false){for(const p of wall){if(!p.active)continue;p.ignition=reduced?1:Math.min(1,p.ignition+dt*3.5);const flicker=reduced?1:.90+.12*Math.sin(time*7+p.index*1.7)+.07*Math.sin(time*13+p.index);p.fire.scale.set(1,Math.max(.02,p.ignition*flicker),1);p.fire.rotation.y=reduced?0:time*.75+p.index;for(let j=0;j<p.embers.length;j++){const u=(time*.7+j*.25+p.index*.17)%1;p.embers[j].visible=!reduced;p.embers[j].position.set(Math.sin(u*6+p.index)*.17,.3+u*.9,Math.cos(u*7+p.index)*.14);p.embers[j].scale.setScalar(1-u);}}}
