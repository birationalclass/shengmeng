// Irregular submerged reef patches in site-plan metres, away from the dry shore.
const patches=[[67,-7,4.1,2.2],[73,5,3.4,4.2],[63,15,2.9,2.1],[49,30,4.3,2.7],[58,-22,3.4,2.2]];
const smooth=(x)=>{x=Math.max(0,Math.min(1,x));return x*x*(3-2*x);};
export function reefMask(x,z){let result=0;for(const[a,b,rx,rz]of patches){const qx=(x-a)/rx,qz=(z-b)/rz;const radius=Math.hypot(qx,qz)+.12*Math.sin(x*1.7+Math.sin(z*1.1))+.08*Math.sin(z*2.3);result=Math.max(result,1-smooth((radius-.38)/.68));}return result;}
export const reefGLSL=`float reefMask(vec2 p){float reef=0.;${patches.map(([x,z,rx,rz])=>`{vec2 q=(p-vec2(${x.toFixed(1)},${z.toFixed(1)}))/vec2(${rx.toFixed(1)},${rz.toFixed(1)});float r=length(q)+.12*sin(p.x*1.7+sin(p.y*1.1))+.08*sin(p.y*2.3);reef=max(reef,1.-smoothstep(.38,1.06,r));}`).join('')}return reef;}`;
