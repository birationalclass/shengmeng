export function blackboardPixelRatio(dpr,width,height,focused=false){
 const ceiling=focused?2:1.25,budget=focused?3000000:1600000;
 return Math.max(1,Math.min(dpr||1,ceiling,Math.sqrt(budget/Math.max(1,width*height))));
}
export class BlackboardFrameBudget{
 constructor(){this.maxFPS=60;this.dirty=true;this.lastUpdate=-Infinity;this.lastDraw=-Infinity;this.signature=null;this.frames=0;}
 invalidate(){this.dirty=true;}
 cadence({hidden=false,moving=false,playing=false,phase='',busy=false}={}){return hidden?0:Math.min(this.maxFPS,moving||phase==='lift'&&playing?60:busy||playing&&['write','erase'].includes(phase)?30:playing?15:2);}
 updateDue(stamp,state){const fps=this.cadence(state);if(!fps)return false;if(!this.dirty&&stamp-this.lastUpdate<1000/fps-1)return false;this.lastUpdate=stamp;return true;}
 drawDue(stamp,signature){if(!this.dirty&&signature===this.signature)return false;this.dirty=false;this.signature=signature;this.lastDraw=stamp;this.frames++;return true;}
}
