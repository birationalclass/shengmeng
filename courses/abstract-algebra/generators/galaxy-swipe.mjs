export function verticalDestination({dx,dy,index,count,passed,required}){
 if(Math.abs(dy)<48||Math.abs(dy)<=Math.abs(dx)*1.2)return null;
 if(dy>0&&passed<required)return 'locked';
 const target=index+(dy>0?1:-1);return target>=0&&target<count?target:null;
}
export function bindPortraitSwipe({host=window,getState,onSelect,onLocked}){
 let start=null;
 host.addEventListener('pointerdown',e=>{start=null;if(!e.isPrimary||e.pointerType==='mouse'||host.innerWidth>750||host.innerHeight<=host.innerWidth)return;
 if(e.target.closest('button,a,input,select,textarea,dialog,#stellarChallenge')||document.querySelector('dialog[open]'))return;
 start={id:e.pointerId,x:e.clientX,y:e.clientY};},{passive:true});
 host.addEventListener('pointercancel',()=>{start=null;},{passive:true});
 host.addEventListener('pointerup',e=>{const origin=start;start=null;if(!origin||origin.id!==e.pointerId||host.innerHeight<=host.innerWidth)return;const state=getState();if(!state)return;
 const target=verticalDestination({...state,dx:e.clientX-origin.x,dy:e.clientY-origin.y});if(target==='locked')onLocked();else if(target!==null)onSelect(target);
 },{passive:true});
}
