// Shared, deterministic mineral maps; generated only on selecting the crystal scheme.
// No downloads, transmission framebuffer, per-frame noise or narration-time work.
let pixels;
function noise(x,y){const n=Math.sin(x*127.1+y*311.7)*43758.5453;return n-Math.floor(n);}
function field(x,y){const ix=Math.floor(x),iy=Math.floor(y),u=x-ix,v=y-iy,s=u*u*(3-2*u),t=v*v*(3-2*v);return (noise(ix,iy)*(1-s)+noise(ix+1,iy)*s)*(1-t)+(noise(ix,iy+1)*(1-s)+noise(ix+1,iy+1)*s)*t;}
export function mineralPixels(){
 if(pixels)return pixels;
 const width=1024,height=512,quartz=new Uint8Array(width*height*4),relief=new Uint8Array(quartz.length),marble=new Uint8ClampedArray(quartz.length);
 for(let y=0;y<height;y++)for(let x=0;x<width;x++){
  const u=x/width,v=y/height,n=field(u*13,v*11),fine=field(u*59,v*47),cloud=field(u*6+.3,v*7+.8),i=(y*width+x)*4;
  const px=u*24+(n-.5)*.8,py=v*16+(cloud-.5)*.7,cx=Math.floor(px),cy=Math.floor(py);let d1=9,d2=9,facet=0;
  for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){const a=cx+dx,b=cy+dy,d=Math.hypot(px-a-noise(a,b),py-b-noise(a+41,b+19));if(d<d1){d2=d1;d1=d;facet=noise(a+12,b+7);}else if(d<d2)d2=d;}
  const vein=Math.exp(-Math.pow((d2-d1)/.024,2)),veil=Math.pow(Math.max(0,cloud-.28),1.4),light=183+cloud*38+n*13+facet*19+vein*20;
  quartz.set([Math.min(255,light+5+veil*7),Math.min(255,light+1),Math.min(255,light+6+facet*4),255],i);
  const bump=Math.round(128+(facet-.5)*7+vein*8);relief.set([bump,bump,bump,255],i);
  const warped=u*9+v*5+(n-.5)*1.4+(fine-.5)*.18,wave=Math.abs(Math.sin(warped*Math.PI)),thread=Math.exp(-Math.pow(wave/.035,2)),branch=Math.exp(-Math.pow(Math.abs(Math.sin((v*15-u*4+cloud)*Math.PI))/.025,2))*.28;
  const stone=22+n*7+fine*2+Math.min(1,thread+branch)*18;marble.set([Math.round(stone),Math.round(stone+1),Math.round(stone+3),255],i);
 }
 return pixels={width,height,quartz,relief,marble};
}
export function createMineralMaps(T,anisotropy=1){
 const p=mineralPixels(),make=(bytes,color)=>{const t=new T.DataTexture(bytes,p.width,p.height);if(color)t.colorSpace=T.SRGBColorSpace;t.wrapS=t.wrapT=T.RepeatWrapping;t.generateMipmaps=true;t.minFilter=T.LinearMipmapLinearFilter;t.anisotropy=Math.min(8,anisotropy);t.needsUpdate=true;return t;};
 return {quartz:make(p.quartz,true),relief:make(p.relief,false)};
}
let stoneCanvas,mineralImages;
export function loadMineralImages(){
 return mineralImages||(mineralImages=Promise.all(['white-quartz.jpg','black-stone.jpg'].map(name=>new Promise((resolve,reject)=>{const image=new Image();image.onload=()=>resolve(image);image.onerror=()=>reject(Error('矿物材质加载失败：'+name));image.src=new URL('./assets/materials/'+name,import.meta.url).href;}))).then(([quartz,stone])=>{stoneCanvas=document.createElement('canvas');stoneCanvas.width=stone.naturalWidth;stoneCanvas.height=stone.naturalHeight;const c=stoneCanvas.getContext('2d');c.drawImage(stone,0,0);c.globalCompositeOperation='multiply';c.fillStyle='#6b6b6b';c.fillRect(0,0,stoneCanvas.width,stoneCanvas.height);c.globalCompositeOperation='source-over';return {quartz,stone};}).catch(error=>{mineralImages=null;throw error;}));
}
export function paintStoneBoard(ctx,w,h){
 if(!stoneCanvas){const p=mineralPixels();stoneCanvas=document.createElement('canvas');stoneCanvas.width=p.width;stoneCanvas.height=p.height;stoneCanvas.getContext('2d').putImageData(new ImageData(p.marble,p.width,p.height),0,0);}
 ctx.drawImage(stoneCanvas,0,0,w,h);
}
export const isCrystalScheme=tone=>tone==='crystal-black';
export function setTrackScheme(track,material,enabled){
 // Keep the original open metal channels intact for wood schemes. Crystal uses
 // its own modeled bevelled rack rather than recoloring these old channels.
 for(const child of track.children)child.visible=child.userData.crystalRack?enabled:!enabled;
}
const environments=new WeakMap();
export function acquireQuartzEnvironment(T,renderer){
 let entry=environments.get(renderer);
 if(!entry){
  const scene=new T.Scene();scene.background=new T.Color('#666773');
  const resources=[],panel=(w,h,p,color)=>{const geometry=new T.PlaneGeometry(w,h),material=new T.MeshBasicMaterial({color:new T.Color(...color),side:T.DoubleSide}),mesh=new T.Mesh(geometry,material);mesh.position.fromArray(p);mesh.lookAt(0,0,0);scene.add(mesh);resources.push(geometry,material);};
  // Broad window/ceiling reflections give the bevels readable optical depth.
  // This cube is baked once; it does not add lights or change the classroom.
  panel(5,8,[-5,2,1],[4.2,3.9,3.6]);panel(3,7,[5,1,-3],[1.8,2.2,3.0]);panel(8,2,[0,5,0],[2.9,2.8,3.2]);panel(4,6,[0,1,6],[.16,.18,.23]);
  const pmrem=new T.PMREMGenerator(renderer),target=pmrem.fromScene(scene,.025,.1,50);pmrem.dispose();resources.forEach(r=>r.dispose());entry={target,refs:0};environments.set(renderer,entry);
 }
 entry.refs++;let released=false;return {texture:entry.target.texture,dispose(){if(released)return;released=true;if(--entry.refs===0){entry.target.dispose();environments.delete(renderer);}}};
}
