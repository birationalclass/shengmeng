export function photoDimensions(width,height,limit=8192){
 const scale=Math.min(3840/Math.max(width,height),limit/Math.max(width,height),Math.sqrt(8294400/(width*height)));
 return {width:Math.max(1,Math.floor(width*scale)),height:Math.max(1,Math.floor(height*scale)),scale};
}
export function capturePhoto(renderer,scene,camera){
 const size=renderer.getSize({set(x,y){this.x=x;this.y=y;return this;}}),ratio=renderer.getPixelRatio();
 const gl=renderer.getContext(),limit=Math.min(renderer.capabilities.maxTextureSize,gl.getParameter(gl.MAX_RENDERBUFFER_SIZE));
 const target=photoDimensions(size.x,size.y,limit),copy=document.createElement('canvas');
 try{
  renderer.setDrawingBufferSize(size.x,size.y,target.scale);
  renderer.render(scene,camera);
  copy.width=renderer.domElement.width;copy.height=renderer.domElement.height;
  const context=copy.getContext('2d');if(!context)throw Error('无法创建照片');
  context.drawImage(renderer.domElement,0,0);
 }finally{renderer.setDrawingBufferSize(size.x,size.y,ratio);renderer.render(scene,camera);}
 return new Promise((resolve,reject)=>copy.toBlob(blob=>blob?resolve(blob):reject(Error('照片生成失败')),'image/png'));
}
export function downloadPhoto(blob){
 const url=URL.createObjectURL(blob),link=document.createElement('a');
 link.href=url;link.download='数学难民营-'+new Date().toISOString().replace(/[:.]/g,'-')+'.png';document.body.append(link);link.click();link.remove();setTimeout(()=>URL.revokeObjectURL(url),60000);
}
