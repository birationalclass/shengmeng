import {visualMotion} from './visual-style.js?v=41';

// A whole chain of filtered degrees in the existing K coordinate plane.
// Degree five includes K^{5,0}; never truncate a direct sum at the grid edge.
export function subcomplexDiagram({p,point,region,label,node}){
 const first=Math.max(0,p),last=Math.min(5,first+4);
 let overlays='',edges='',terms='';
 for(let n=first;n<=last;n++){
  const start=point(first,n-first),end=point(n,0),order=n-first;
  overlays+=`<g class="subcomplex-degree" data-chain-order="${order}"><path class="diag-box" data-degree="${n}" data-first="${first}" data-last="${n}" d="${region(start,end,0)}"/>${label(start[0]-94,start[1],String.raw`F^{${p}}C^{${n}}`,110,34,true)}</g>`;
  if(n===last)continue;
  const next=point(first,n+1-first),x=start[0],y1=start[1]-22,y2=next[1]+22;
  edges+=`<g class="subcomplex-map" data-chain-order="${order}" data-from-degree="${n}" data-to-degree="${n+1}"><path class="subcomplex-arrow" d="M${x},${y1} V${y2}" fill="none" stroke="var(--teal)" stroke-width="3.2" stroke-linecap="round"/><path d="M${x-5},${y2+7} L${x},${y2} L${x+5},${y2+7}" fill="none" stroke="var(--teal)" stroke-width="3.2" stroke-linecap="round" stroke-linejoin="round"/>${label(x+26,(y1+y2)/2,'D',34,26,true)}</g>`;
 }
 // Reserve the preceding column for degree labels; keep the remaining K
 // blocks at their original positions, including dim context above the chain.
 for(let i=first;i<=Math.max(4,last);i++)for(let j=0;j<=4;j++){
  if(i>4&&i+j>last)continue;
  terms+=node(i,j,`K^{${i},${j}}`,{muted:i+j>last});
 }
 return {overlays,edges,terms};
}

function entranceTargets(host){
 return [...host.querySelectorAll('.subcomplex-degree,.subcomplex-map')].map(group=>{
  const targets=[group];
  for(const anchor of group.querySelectorAll('.math-anchor')){
   const d=anchor.dataset,key=[d.x,d.y,d.width,d.height].join(':');
   const label=[...host.querySelectorAll('.diagram-label')].find(el=>el.dataset.key===key);
   if(label)targets.push(label);
  }
  return {group,targets};
 });
}
export function prepareSubcomplexEntrance(host){
 for(const {targets} of entranceTargets(host))for(const target of targets){
  target.getAnimations().forEach(a=>a.cancel());target.style.opacity='0';
 }
}
export function animateSubcomplexEntrance(host){
 const motion=visualMotion(),animations=[];
 for(const {group,targets} of entranceTargets(host)){
  const order=Number(group.dataset.chainOrder),map=group.classList.contains('subcomplex-map');
  for(const target of targets){
   target.getAnimations().forEach(a=>a.cancel());target.style.opacity='1';
   if(!motion.reduced)animations.push(target.animate([{opacity:0},{opacity:1}],{duration:motion.enter,delay:order*160+(map?140:0),easing:motion.easing,fill:'backwards'}));
  }
 }
 return animations;
}
