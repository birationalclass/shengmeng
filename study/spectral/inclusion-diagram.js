import {fitDiagramSurface} from './diagram-viewport.js?v=67';
import {visualMotion} from './visual-style.js?v=41';

// One coordinate surface owns both the boxes and their mathematical labels.
// Keep the preceding diagram intact until its exit has finished.
export function createInclusionDiagram({viewport,diagram,math,language}){
 const R=String.raw,host=document.createElement('div');
 host.id='inclusionDiagram';host.hidden=true;host.inert=true;viewport.append(host);
 let active=false,epoch=0,animations=[],drawnLanguage='';
 const fit=()=>fitDiagramSurface(viewport,host,'--inclusion-scale');
 new ResizeObserver(fit).observe(viewport);
 const label=(x,y,tex,kind='')=>`<span class="inclusion-label ${kind}" style="left:${x}px;top:${y}px">${math(tex)}</span>`;
 function draw(){
  let shapes='',labels='';
  const columns=[180,420,660],degrees=['n-1','n','n+1'];
  for(const [row,y] of [170,355].entries()){
   for(let i=0;i<3;i++){
    const x=columns[i];
    shapes+=`<rect class="inclusion-term ${row?'total':'filtered'}" x="${x-74}" y="${y-28}" width="148" height="56" rx="9"/>`;
    labels+=label(x,y,`${row?'':'F^p'}C^{${degrees[i]}}`,'term');
   }
   labels+=label(34,y,R`\cdots`)+label(806,y,R`\cdots`);
   for(const [from,to] of [[60,100],[262,338],[502,578],[740,780]]){
    shapes+=`<path class="inclusion-arrow horizontal" d="M${from},${y} H${to}" marker-end="url(#inclusion-tip)"/>`;
    labels+=label((from+to)/2,y-23,'D','map');
   }
  }
  for(let i=0;i<3;i++){
   const x=columns[i];
   shapes+=`<path class="inclusion-arrow vertical" d="M${x+7},211 Q${x+7},202 ${x},202 V319" marker-end="url(#inclusion-tip)"/>`;
   labels+=label(x+48,262,R`\iota_p^{${degrees[i]}}`,'map inclusion');
  }
  host.innerHTML=`<div class="inclusion-scene"><svg viewBox="0 0 840 525" role="img" aria-label="${language()==='en'?'Inclusion of the filtered subcomplex into the total complex; the diagram commutes':'滤过子复形到总复形的包含；图表交换'}"><defs><marker id="inclusion-tip" markerUnits="userSpaceOnUse" markerWidth="10" markerHeight="10" refX="8" refY="5" orient="auto"><path d="M2,2 L8,5 L2,8" fill="none" stroke="currentColor" stroke-width="1.5"/></marker></defs>${shapes}</svg>${labels}</div>`;
  drawnLanguage=language();fit();
 }
 function cancel(){epoch++;animations.forEach(a=>a.cancel());animations=[];}
 function restore(){diagram.style.removeProperty('opacity');diagram.style.removeProperty('visibility');}
 async function fade(el,from,to,duration,token){
  const a=el.animate([{opacity:from},{opacity:to}],{duration,easing:visualMotion().easing,fill:'forwards'});animations.push(a);
  await a.finished.catch(()=>{});if(token!==epoch)return false;
  el.style.opacity=String(to);a.cancel();animations=animations.filter(x=>x!==a);return true;
 }
 return {
  sync(s){
   const next=!s.cover&&s.module==='initial'&&s.effect==='inclusion';
   if(next===active){if(active&&drawnLanguage!==language())draw();return active;}
   cancel();active=next;host.hidden=!active;restore();
   if(active){draw();host.style.opacity='0';host.dataset.phase='waiting';}
   else{host.style.opacity='0';host.dataset.phase='inactive';}
   return active;
  },
  prepare(){if(!active)return;cancel();restore();host.style.opacity='0';host.dataset.phase='waiting';},
  async play(){
   if(!active)return;cancel();const token=epoch,motion=visualMotion();
   host.dataset.phase='exiting';
   if(!await fade(diagram,getComputedStyle(diagram).opacity,0,motion.reduced?0:motion.exit,token))return;
   diagram.style.visibility='hidden';host.dataset.phase='entering';
   if(!await fade(host,0,1,motion.reduced?0:motion.enter,token))return;
   host.dataset.phase='settled';
  }
 };
}
