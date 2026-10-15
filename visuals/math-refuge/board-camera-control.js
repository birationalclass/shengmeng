import {reportControlLayout} from './report-voice.js?v=board-controls-3';
import {SCREEN_COLORS,beginControlInk} from './smart-screen-style.js?v=unframed-controls-1';
export function createBoardCameraControl(T,parent,column){
 const canvas=document.createElement('canvas');canvas.width=canvas.height=128;
 const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
 const material=new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false});
 const mesh=new T.Mesh(new T.PlaneGeometry(.6,.6),material);mesh.name='Smart glass automatic board camera';
 mesh.userData={action:'camera:toggle',column,smartGlass:true};parent.add(mesh);mesh.visible=false;
 const zoomControls=[['zoomOut','camera:farther',1],['zoomIn','camera:closer',-1]].map(([key,action,direction])=>{
  const surface=document.createElement('canvas');surface.width=surface.height=128;const map=new T.CanvasTexture(surface);map.colorSpace=T.SRGBColorSpace;
  const button=new T.Mesh(new T.PlaneGeometry(.34,.3),new T.MeshBasicMaterial({map,transparent:true,depthWrite:false,toneMapped:false}));
  button.name=direction>0?'Board camera farther (+)':'Board camera closer (-)';button.userData={action,column,smartGlass:true};button.visible=false;parent.add(button);return{key,direction,mesh:button,canvas:surface,texture:map,last:null};
 });
 let last=null;
 return {mesh,meshes:[mesh,...zoomControls.map(c=>c.mesh)],update(enabled,visible,withVoice=true,zoom=0){
  const p=reportControlLayout(column,withVoice).camera;mesh.position.set(p.x,p.y,p.z);mesh.updateMatrix();mesh.visible=visible;
  mesh.userData.label=enabled?'自动镜头 · 开启（点击关闭）':'自动镜头 · 关闭（点击开启）';mesh.userData.active=enabled;
  for(const control of zoomControls){const p=reportControlLayout(column)[control.key];control.mesh.position.set(p.x,p.y,p.z);control.mesh.updateMatrix();control.mesh.visible=visible;
   const limited=control.direction>0?zoom>=1:zoom<=0;control.mesh.userData.limit=limited;control.mesh.userData.label=control.direction>0?'＋ 拉远 · 最远显示全部黑板':'− 拉近 · 最近保留完整当前黑板';
   if(control.last===limited)continue;control.last=limited;const c=control.canvas.getContext('2d');c.clearRect(0,0,128,128);beginControlInk(c);c.strokeStyle=limited?SCREEN_COLORS.muted:SCREEN_COLORS.text;c.lineWidth=5;c.lineCap='square';c.beginPath();c.moveTo(40,64);c.lineTo(88,64);if(control.direction>0){c.moveTo(64,40);c.lineTo(64,88);}c.stroke();c.restore();control.texture.needsUpdate=true;
  }
  if(last===enabled)return;last=enabled;const c=canvas.getContext('2d');c.clearRect(0,0,128,128);
  beginControlInk(c);c.strokeStyle=enabled?SCREEN_COLORS.active:SCREEN_COLORS.muted;c.lineWidth=3;c.lineCap='square';c.lineJoin='miter';
  c.beginPath();for(const [x,y,sx,sy] of [[33,36,1,1],[95,36,-1,1],[33,92,1,-1],[95,92,-1,-1]]){c.moveTo(x+17*sx,y);c.lineTo(x,y);c.lineTo(x,y+17*sy);}c.stroke();
  c.beginPath();c.arc(64,64,10,0,Math.PI*2);c.stroke();
  if(!enabled){c.beginPath();c.moveTo(41,87);c.lineTo(87,41);c.stroke();}c.restore();texture.needsUpdate=true;
 },dispose(){zoomControls.forEach(c=>{c.mesh.removeFromParent();c.mesh.geometry.dispose();c.mesh.material.dispose();c.texture.dispose();});mesh.removeFromParent();mesh.geometry.dispose();material.dispose();texture.dispose();}};
}
