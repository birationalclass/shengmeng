import {TRAY_DOCK} from './board-tray-layout.js';
import {BOARD_LAYOUT} from './lecture-state.js';
import {BOARD_MOUNT_OFFSET} from './board-hardware.js';
const clamp=value=>Math.max(0,Math.min(1,Number(value)||0));
export function stepBoardCameraZoom(value,direction){return clamp(Math.round((clamp(value)+Math.sign(direction)*.1)*10)/10);}
// Keep the optical axis through the active board center at every zoom level.
// The nearest limit fits its complete outer frame without tray/toolbar padding.
export function boardCameraFrame(aspect,fov=57,zoom=0,{column=0,boardY=BOARD_LAYOUT.low,boardZ=-10.45+BOARD_MOUNT_OFFSET,frameMargin=.04+.0025*Math.SQRT2}={}){
 const amount=clamp(zoom),cx=22.4+5.6*Math.max(0,Math.min(2,column));
 const nearX=BOARD_LAYOUT.width/2+frameMargin,nearY=BOARD_LAYOUT.height/2+frameMargin;
 const farX=Math.max(cx-19.6,36.4-cx),farY=Math.max(boardY-(TRAY_DOCK.bottom-.06),BOARD_LAYOUT.high+BOARD_LAYOUT.height/2+frameMargin-boardY);
 const halfX=nearX+(farX-nearX)*amount,halfY=nearY+(farY-nearY)*amount;
 const bounds={left:cx-halfX,right:cx+halfX,bottom:boardY-halfY,top:boardY+halfY};
 const radius=Math.max(halfY,halfX/Math.max(.1,aspect)),tangent=Math.max(Math.tan(Math.max(10,Math.min(120,fov))*Math.PI/360),radius/14);
 const frontOffset=.016+Math.max(0,-10.29+BOARD_MOUNT_OFFSET-boardZ)*amount,distance=radius/tangent+frontOffset;
 return {zoom:amount,bounds,distance,fov:Math.atan(tangent)*360/Math.PI,x:cx,y:boardY,z:boardZ};
}
