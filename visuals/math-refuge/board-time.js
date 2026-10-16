import {trayControlLayout,placeTrayControl} from './board-tray-layout.js';
import {SCREEN_COLORS,SCREEN_MONO} from './smart-screen-style.js?v=unframed-controls-1';
export function elapsedLabel(seconds){const n=Math.max(0,Math.floor(Number(seconds)||0)),s=String(n%60).padStart(2,'0'),m=Math.floor(n/60);return m>=60?Math.floor(m/60)+':'+String(m%60).padStart(2,'0')+':'+s:String(m).padStart(2,'0')+':'+s;}
export function boardTimeLabel(state,clock){return state?.duration>0?elapsedLabel(state.time)+' / '+elapsedLabel(state.duration):'本板 '+elapsedLabel(clock?.elapsed)+' / '+elapsedLabel(clock?.duration);}
export function localTimeLabel(now=new Date()){return [now.getHours(),now.getMinutes(),now.getSeconds()].map(n=>String(n).padStart(2,'0')).join(':');}
export function boardTimePosition(column){return trayControlLayout(column).time;}
export function createBoardTimePanel(T,parent,column){
 const canvas=document.createElement('canvas');canvas.width=512;canvas.height=96;const ctx=canvas.getContext('2d'),texture=new T.CanvasTexture(canvas);texture.colorSpace=T.SRGBColorSpace;
 const mesh=new T.Mesh(new T.PlaneGeometry(1.95,.32),new T.MeshBasicMaterial({map:texture,transparent:true,depthWrite:false,toneMapped:false}));mesh.name='Current course or report elapsed time';mesh.userData={action:'board:time',column,smartGlass:true,label:'点击显示当前时间'};const p=boardTimePosition(column);placeTrayControl(mesh,p);parent.add(mesh);mesh.visible=false;let last='';
 return{mesh,get text(){return last;},update(state,clock,visible,local=false,now){mesh.visible=visible;mesh.userData.label=local?'点击恢复课程进度':'点击显示当前时间';const text=local?localTimeLabel(now):boardTimeLabel(state,clock);if(text===last)return;last=text;ctx.clearRect(0,0,512,96);ctx.font='36px '+SCREEN_MONO;ctx.textAlign='center';ctx.textBaseline='alphabetic';ctx.fillStyle=SCREEN_COLORS.text;const metrics=ctx.measureText?.(text),ascent=metrics?.actualBoundingBoxAscent??26,descent=metrics?.actualBoundingBoxDescent??2;ctx.fillText(text,256,48+(ascent-descent)/2);texture.needsUpdate=true;},dispose(){mesh.parent?.remove(mesh);mesh.geometry.dispose();mesh.material.dispose();texture.dispose();}};
}
