import {reportControlLayout} from './report-voice.js?v=smart-voice-9';
export function createBoardCameraControl(T,parent,column){
 const canvas=document.createElement('canvas');canvas.width=canvas.height=128;
 const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
 const material=new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false});
 const mesh=new T.Mesh(new T.PlaneGeometry(.6,.6),material);mesh.name='Smart glass automatic board camera';
 mesh.userData={action:'camera:toggle',column,smartGlass:true};parent.add(mesh);mesh.visible=false;
 let last=null;
 return {mesh,update(enabled,visible,withVoice=true){
  const p=reportControlLayout(column,withVoice).camera;mesh.position.set(p.x,p.y,p.z);mesh.updateMatrix();mesh.visible=visible;
  mesh.userData.label=enabled?'自动镜头 · 开启（点击关闭）':'自动镜头 · 关闭（点击开启）';mesh.userData.active=enabled;
  if(last===enabled)return;last=enabled;const c=canvas.getContext('2d');c.clearRect(0,0,128,128);
  c.strokeStyle=enabled?'#f0e4ca':'#a6aaa1';c.lineWidth=4;c.lineCap='round';c.lineJoin='round';
  c.beginPath();for(const [x,y,sx,sy] of [[33,36,1,1],[95,36,-1,1],[33,92,1,-1],[95,92,-1,-1]]){c.moveTo(x+17*sx,y);c.lineTo(x,y);c.lineTo(x,y+17*sy);}c.stroke();
  c.beginPath();c.arc(64,64,10,0,Math.PI*2);c.stroke();
  if(!enabled){c.beginPath();c.moveTo(41,87);c.lineTo(87,41);c.stroke();}texture.needsUpdate=true;
 },dispose(){mesh.removeFromParent();mesh.geometry.dispose();material.dispose();texture.dispose();}};
}
