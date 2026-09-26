export const VIDEO_SITES=[
 {id:'bilibili',label:'bilibili',color:'#fb7299',url:'https://www.bilibili.com/'},
 {id:'iqiyi',label:'iQIYI',color:'#43d76b',url:'https://www.iqiyi.com/'},
 {id:'tencent',label:'腾讯视频',color:'#82d9ed',url:'https://v.qq.com/'}
];
export class ScreenMode{
 constructor(){this.power=true;this.mode='home';this.reportAlpha=0;this.mediaAlpha=0;this.idle=0;this.brightness=1;}
 wake(){this.idle=0;}
 action(action){this.wake();if(action==='screen:power'){this.power=!this.power;return true;}if(action==='screen:report'||action==='screen:media'){this.power=true;this.mode=action.slice(7);return true;}return false;}
 update(dt,stored){dt=Math.max(0,Math.min(.1,dt));this.idle+=dt;
  const toward=(a,b)=>a+(b-a)*(1-Math.exp(-dt*10));
  this.reportAlpha=toward(this.reportAlpha,this.power&&this.mode==='report'?1:0);
  this.mediaAlpha=toward(this.mediaAlpha,this.power&&this.mode==='media'&&stored>.98?1:0);
  this.brightness=toward(this.brightness,this.idle>4?.22:1);
 }
}
export function createSmartGlassHub(T,root,{reports,storage,onStore}){
 const state=new ScreenMode(),items=[];
 function label(action,x,y,w,h,draw){
  const canvas=document.createElement('canvas');canvas.width=512;canvas.height=256;
  const c=canvas.getContext('2d');draw(c);
  const texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
  const mesh=new T.Mesh(new T.PlaneGeometry(w,h),new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false}));
  mesh.position.set(x,y,-11.30);mesh.name=action;mesh.userData={action,smartGlass:true};root.add(mesh);items.push(mesh);return mesh;
 }
 const ink=c=>{c.strokeStyle='#ecdfc3';c.fillStyle='#ecdfc3';c.lineWidth=12;c.lineCap='round';};
 const power=label('screen:power',28,-1.0,.75,.375,c=>{ink(c);c.beginPath();c.arc(256,133,65,-Math.PI*.32,Math.PI*1.32);c.stroke();c.beginPath();c.moveTo(256,40);c.lineTo(256,123);c.stroke();});
 const report=label('screen:report',27.3,-1.0,.64,.32,c=>{ink(c);c.strokeRect(182,43,148,172);for(let i=0;i<3;i++){c.beginPath();c.moveTo(211,88+i*39);c.lineTo(299,88+i*39);c.stroke();}});
 const media=label('screen:media',28.7,-1.0,.64,.32,c=>{ink(c);c.strokeRect(155,52,202,150);c.beginPath();c.moveTo(237,88);c.lineTo(291,127);c.lineTo(237,167);c.closePath();c.fill();});
 const sites=VIDEO_SITES.map((site,i)=>label('screen:site:'+site.id,24.5+i*3.5,2.05,2.8,1.4,c=>{
  c.fillStyle=site.color;c.textAlign='center';c.textBaseline='middle';c.font=(site.id==='bilibili'?'italic 76px':'bold 83px')+' sans-serif';c.fillText(site.label,256,128);

 }));
 function opacity(mesh,a){mesh.visible=a>.005;mesh.traverse(o=>{if(o.material?.colorWrite!==false&&o.material?.opacity!==undefined)o.material.opacity=a;if(o.material?.uniforms?.strength&&a<.99)o.material.uniforms.strength.value=0;});}
 function update(dt,stored){state.update(dt,stored);reports.forEach(m=>opacity(m,state.reportAlpha));sites.forEach(m=>opacity(m,state.mediaAlpha));power.material.opacity=state.brightness*(state.power?1:.65);for(const m of [report,media])opacity(m,state.power?1:0);if(storage)opacity(storage,state.power?1:0);}
 update(0,1);
 return {state,wake:()=>state.wake(),update,
  get targets(){return items.filter(m=>m.visible&&(m===power||state.power)&&(sites.includes(m)?state.mode==='media'&&state.mediaAlpha>.9:true));},
  action(a){if(!state.action(a))return false;if(a==='screen:media')onStore();return true;},
  report(){state.action('screen:report');},
  dispose(){for(const m of items){m.geometry.dispose();m.material.map.dispose();m.material.dispose();root.remove(m);}}
 };
}
