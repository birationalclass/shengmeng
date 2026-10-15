// Canvas y points down: upright, then 15 degrees counterclockwise on the board.
export const ERASER_ANGLE=-7*Math.PI/12;
export const FELT_HALF_WIDTH=47,FELT_HALF_HEIGHT=28,FELT_CORE=.78;
export function feltCoreBounds(angle=ERASER_ANGLE){
 const a=FELT_HALF_WIDTH*FELT_CORE,b=FELT_HALF_HEIGHT*FELT_CORE,c=Math.cos(angle),s=Math.sin(angle),x=Math.hypot(a*c,b*s),y=Math.hypot(a*s,b*c);
 const q=Math.max(...[-1,1].flatMap(sx=>[-1,1].map(sy=>((sx*x*c+sy*y*s)/a)**2+((-sx*x*s+sy*y*c)/b)**2))),k=1/Math.sqrt(q);
 return{x:Math.floor(x*k)-2,y:Math.floor(y*k)-2};
}
export function feltContains(x,y,pose,core=false){const c=Math.cos(pose.angle),s=Math.sin(pose.angle),dx=x-pose.x,dy=y-pose.y;return((dx*c+dy*s)/FELT_HALF_WIDTH)**2+((-dx*s+dy*c)/FELT_HALF_HEIGHT)**2<=(core?FELT_CORE:1)**2;}
export function stampFelt(ctx,pose){
 ctx.save();ctx.translate(pose.x,pose.y);ctx.rotate(pose.angle);ctx.scale(FELT_HALF_WIDTH,FELT_HALF_HEIGHT);
 const gradient=ctx.createRadialGradient(0,0,FELT_CORE,0,0,1);gradient.addColorStop(0,'rgba(255,255,255,1)');gradient.addColorStop(1,'rgba(255,255,255,0)');ctx.fillStyle=gradient;ctx.fillRect(-1,-1,2,2);ctx.restore();
}
