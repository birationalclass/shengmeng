// Resource upgrades wait for a settled camera, including rotation-only gestures.
export class RenderChangeGate{
 constructor(){this.quiet=0;this.previous=null;this.ready=false;}
 sample(position,rotation,dt,blocked=false){
  const p=[...position,...rotation],old=this.previous;this.previous=p;
  const moved=!old||Math.hypot(...p.slice(0,3).map((v,i)=>v-old[i]))>.002||Math.min(Math.hypot(...p.slice(3).map((v,i)=>v-old[i+3])),Math.hypot(...p.slice(3).map((v,i)=>v+old[i+3])))>.00002;
  this.quiet=blocked||moved?0:this.quiet+Math.max(0,Math.min(.1,dt));
  return this.ready=this.quiet>=2;
 }
}
