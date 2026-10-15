// The gutter keeps the existing chalk/eraser contact heights. The front shoulder
// carries a single inclined glass strip; visible ink and raycast targets share it.
export const TRAY_DOCK={width:5.42,panelWidth:5.20,panelHeight:.125,y:.6544,z:-10.3983,tilt:Math.atan(.08/.12),bottom:.50};
const slots={language:[-2.31,.42,.25],previous:[-1.75,.28,.28],voice:[-1.29,.30,.30],next:[-.83,.28,.28],time:[.12,1.42,.24],camera:[1.25,.28,.28],zoomOut:[1.66,.24,.24],zoomIn:[2.00,.24,.24],reveal:[2.37,.30,.30]};
export function trayControlLayout(column=0){
 const center=22.4+5.6*Math.max(0,Math.min(2,column)),y=TRAY_DOCK.y+Math.sin(TRAY_DOCK.tilt)*.014,z=TRAY_DOCK.z+Math.cos(TRAY_DOCK.tilt)*.014;
 return{center,...Object.fromEntries(Object.entries(slots).map(([key,[dx,width,height]])=>[key,{x:center+dx,y,z,width,height,tilt:TRAY_DOCK.tilt}]))};
}
export function placeTrayControl(mesh,p){
 mesh.userData.trayControl=true;
 mesh.position.set(p.x,p.y,p.z);mesh.rotation.x=-p.tilt;
 mesh.scale.set(p.width/mesh.geometry.parameters.width,p.height/mesh.geometry.parameters.height,1);mesh.updateMatrix();
}
