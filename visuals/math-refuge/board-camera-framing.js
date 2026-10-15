import {BOARD_LAYOUT} from './lecture-state.js';
const clamp=value=>Math.max(0,Math.min(1,Number(value)||0));
export function stepBoardCameraZoom(value,direction){return clamp(Math.round((clamp(value)+Math.sign(direction)*.1)*10)/10);}
// Fit nested rectangles: every intermediate view contains the entire active board.
// Include its glass controls so the user can always reverse the adjustment.
export function boardCameraFrame(aspect,fov=57,zoom=0,{column=0,boardY=BOARD_LAYOUT.low}={}){
 const amount=clamp(zoom),cx=22.4+5.6*Math.max(0,Math.min(2,column));
 const current={left:cx-2.8,right:cx+2.8,bottom:-.86,top:boardY+BOARD_LAYOUT.height/2+BOARD_LAYOUT.frame};
 const wall={left:19.6,right:36.4,bottom:current.bottom,top:Math.max(current.top,BOARD_LAYOUT.high+BOARD_LAYOUT.height/2+BOARD_LAYOUT.frame)};
 const bounds=Object.fromEntries(Object.keys(current).map(k=>[k,current[k]+(wall[k]-current[k])*amount]));
 // Leave room for the page toolbar; portrait overview widens the lens before backing through the hall wall.
 const extent=Math.max((bounds.top-bounds.bottom)/.82,(bounds.right-bounds.left)/Math.max(.1,aspect)/.96);
 const tangent=Math.max(Math.tan(Math.max(10,Math.min(120,fov))*Math.PI/360),extent/28),distance=extent/2/tangent+.04;
 return {zoom:amount,bounds,distance,fov:Math.atan(tangent)*360/Math.PI,x:(bounds.left+bounds.right)/2,y:(bounds.bottom+bounds.top)/2,z:-10.78};
}
