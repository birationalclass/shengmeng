// Rectangles are in logical board coordinates, independent of texture scale.
export function unionInkRects(rects,width=1536,height=640,pad=5){
 const used=rects.filter(r=>r&&r.every(Number.isFinite));if(!used.length)return null;
 const x=Math.max(0,Math.floor(Math.min(...used.map(r=>r[0]))-pad)),y=Math.max(0,Math.floor(Math.min(...used.map(r=>r[1]))-pad));
 const right=Math.min(width,Math.ceil(Math.max(...used.map(r=>r[0]+r[2]))+pad)),bottom=Math.min(height,Math.ceil(Math.max(...used.map(r=>r[1]+r[3]))+pad));return right>x&&bottom>y?[x,y,right-x,bottom-y]:null;
}
export function changedInkRect(rows,from,to,pose,width=1536,height=640){
 if(from===to)return null;if(from>to||!rows?.length)return[0,0,width,height];
 const first=pose(from).row,last=pose(to).row;
 return unionInkRects(rows.slice(Math.max(0,first),last+1).map(r=>r.strokeRaster?.glyphRect||r),width,height);
}
export const intersectsInk=(r,area)=>!area||r[0]<area[0]+area[2]&&r[0]+r[2]>area[0]&&r[1]<area[1]+area[3]&&r[1]+r[3]>area[1];

// Copy only the changed canvas region into an already allocated GPU texture.
// The small CPU->GPU patch avoids re-uploading a 15 MiB canvas every stroke.
// Three r180 owns the GL state and generates the destination mip chain.
export function createBoardInkUploader(THREE,renderer,{makeCanvas=()=>document.createElement('canvas')}={}){
 const supported=renderer.isWebGLRenderer&&typeof renderer.copyTextureToTexture==='function';let patch=null,source=null;const stats={full:0,partial:0,lastBytes:0,bytes:0,lastUploadMs:0};
 function upload(board,area=null){const started=performance.now(),canvas=board.canvas;
  const scale=canvas.width/1536;
  if(!supported||!board.inkUploaded||!area||area[2]*area[3]>1536*640*.6){board.texture.needsUpdate=true;board.inkUploaded=true;stats.full++;stats.lastBytes=canvas.width*canvas.height*4;}
  else{
   const x=Math.max(0,Math.floor(area[0]*scale)),y=Math.max(0,Math.floor(area[1]*scale)),w=Math.min(canvas.width-x,Math.ceil((area[0]+area[2])*scale)-x),h=Math.min(canvas.height-y,Math.ceil((area[1]+area[3])*scale)-y);
   if(w<=0||h<=0)return;
   if(!patch){patch=makeCanvas();source=new THREE.Texture(patch);}
   if(patch.width!==w)patch.width=w;if(patch.height!==h)patch.height=h;
   const ctx=patch.getContext('2d');ctx.clearRect(0,0,w,h);ctx.drawImage(canvas,x,y,w,h,0,0,w,h);
   renderer.copyTextureToTexture(source,board.texture,null,new THREE.Vector2(x,canvas.height-y-h));stats.partial++;stats.lastBytes=w*h*4;
  }
  stats.bytes+=stats.lastBytes;stats.lastUploadMs=performance.now()-started;
 }
 return{upload,get stats(){return{...stats};},dispose(){source?.dispose();if(patch)patch.width=patch.height=1;}};
}
