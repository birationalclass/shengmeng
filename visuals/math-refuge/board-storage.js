// Ordered interlock: lids must clear the shaft before the assembly moves.
export class BoardStorage {
  constructor(stored=false){this.progress=stored?1:0;this.lid=0;this.phase='idle';}
  update(dt,stored){
    dt=Math.max(0,Math.min(.1,dt));const target=stored?1:0;
    if(this.progress!==target){
      if(this.lid<1){this.phase='opening';this.lid=Math.min(1,this.lid+dt/.85);}
      else {this.phase='moving';const d=dt/4.5;this.progress=target?Math.min(1,this.progress+d):Math.max(0,this.progress-d);}
    }else if(this.lid>0){this.phase='closing';this.lid=Math.max(0,this.lid-dt/.85);}
    else this.phase='idle';
    return this;
  }
  get ready(){return this.phase==='idle'&&this.lid===0;}
}
export function subtractRect(rect,hole){
  const [a,b,c,d]=rect,[e,f,g,h]=hole,x0=Math.max(a,e),x1=Math.min(b,f),z0=Math.max(c,g),z1=Math.min(d,h);
  if(x0>=x1||z0>=z1)return [rect];
  return [[a,x0,c,d],[x1,b,c,d],[x0,x1,c,z0],[x0,x1,z1,d]].filter(([x,y,z,w])=>y-x>1e-7&&w-z>1e-7);
}
