import {SCREEN_COLORS,SCREEN_MONO} from './smart-screen-style.js?v=unframed-controls-1';
export function elapsedLabel(seconds){const n=Math.max(0,Math.floor(Number(seconds)||0)),s=String(n%60).padStart(2,'0'),m=Math.floor(n/60);return m>=60?Math.floor(m/60)+':'+String(m%60).padStart(2,'0')+':'+s:String(m).padStart(2,'0')+':'+s;}
export function boardTimeLabel(state,clock){return state?.duration>0?elapsedLabel(state.time)+' / '+elapsedLabel(state.duration):'本板 '+elapsedLabel(clock?.elapsed)+' / '+elapsedLabel(clock?.duration);}
export function boardTimePosition(column){return{x:22.4+5.6*column,y:-.54,z:-11.302,width:1.95,height:.32};}
export function createBoardTimePanel(T,parent,column){
 const canvas=document.createElement('canvas');canvas.width=512;canvas.height=96;const ctx=canvas.getContext('2d'),texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
 const mesh=new T.Mesh(new T.PlaneGeometry(1.95,.32),new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false}));mesh.name='Current course or report elapsed time';const p=boardTimePosition(column);mesh.position.set(p.x,p.y,p.z);parent.add(mesh);mesh.visible=false;let last='';
 return{mesh,get text(){return last;},update(state,clock,visible){mesh.visible=visible;const text=boardTimeLabel(state,clock);if(text===last)return;last=text;ctx.clearRect(0,0,512,96);ctx.font='36px '+SCREEN_MONO;ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillStyle=SCREEN_COLORS.text;ctx.fillText(text,256,46);texture.needsUpdate=true;},dispose(){mesh.parent?.remove(mesh);mesh.geometry.dispose();mesh.material.dispose();texture.dispose();}};
}
