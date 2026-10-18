// Media time is authoritative; skipping never changes playback intent.
export function boardWaitAt(board,time){
 const wait=board?.waits?.find(w=>Number.isFinite(w.start)&&Number.isFinite(w.end)&&w.end>w.start&&time>=w.start&&time<w.end);
 return wait?{...wait,remaining:wait.end-time}:null;
}
export function classroomWaitAt(manifest,time,page){
 const board=manifest?.boards?.find(b=>b.page===page),wait=boardWaitAt(board,time-(board?.start||0));
 if(wait)return {...wait,start:board.start+wait.start,end:board.start+wait.end,page};
 const activity=manifest?.chapters?.find(c=>c.page===page&&c.kind==='activity'&&c.activityType==='exercise'&&time>=c.start&&time<c.start+c.duration);
 return activity?{start:activity.start,end:activity.start+activity.duration,remaining:activity.start+activity.duration-time,page}:null;
}
export function countdownTextRect(ctx,text,x,y,height,padding=18){return [x-ctx.measureText(text).width/2-padding,y-height,ctx.measureText(text).width+padding*2,height+padding];}
export function containsCountdown(rect,x,y){return !!rect&&x>=rect[0]&&x<=rect[0]+rect[2]&&y>=rect[1]&&y<=rect[1]+rect[3];}
export function createCountdownTargets(T,boards){return boards.map((b,index)=>{const mesh=new T.Mesh(new T.PlaneGeometry(1,1),new T.MeshBasicMaterial({transparent:true,opacity:0,colorWrite:false,depthWrite:false}));mesh.name='Blackboard countdown skip '+index;mesh.position.z=.018;mesh.visible=false;mesh.userData={action:'activity:skip',label:'点击跳过剩余思考',index};b.group.add(mesh);return mesh;});}
export function placeCountdownTarget(mesh,rect,W,H,width,height){mesh.position.x=((rect[0]+rect[2]/2)/W-.5)*width;mesh.position.y=(.5-(rect[1]+rect[3]/2)/H)*height;mesh.scale.set(rect[2]/W*width,rect[3]/H*height,1);}
