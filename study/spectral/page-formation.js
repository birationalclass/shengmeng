import {visualMotion} from './visual-style.js?v=41';
// Split off pi_p(Z_r^{p,q}) inside K^{p,q}, not Z_r itself. Then take
// the quotient by pi_p(B_{r-1}^{p,q}), canonically identified with E_r.
// Tile sizes convey hierarchy, never subspace dimensions.
// The source cards stay fixed; only incoming E cards move. Both use the same
// 840 x 525 geometry and the diagram's single responsive scale.
export function createPageFormation({host,point,math}){
 let layer=null,animations=[],base=[],serial=0,running=false,prepared=null;
 const animate=(el,frames,options)=>{const a=el.animate(frames,{fill:'both',easing:visualMotion().easing,...options});animations.push(a);return a;};
 function clear(){
  serial++;running=false;prepared=null;
  const current=base.filter(el=>el.isConnected).map(el=>[el,getComputedStyle(el).opacity]);
  animations.forEach(a=>a.cancel());animations=[];base=[];
  const old=layer;layer=null;
  if(old){old.removeAttribute('id');if(visualMotion().reduced)old.remove();else old.animate([{opacity:getComputedStyle(old).opacity},{opacity:0}],{duration:220,fill:'forwards'}).finished.then(()=>old.remove(),()=>old.remove());}
  for(const [el,from]of current){const to=getComputedStyle(el).opacity;if(from!==to&&!visualMotion().reduced)el.animate([{opacity:from},{opacity:to}],{duration:220,easing:visualMotion().easing});}
 }
 function prepare(r){
  clear();if(visualMotion().reduced)return;
  base=[...host.querySelectorAll('#diagram-terms .node,.diagram-label-plane .term-label')];
  layer=document.createElement('div');layer.id='pageFormation';layer.className='page-formation';layer.setAttribute('aria-hidden','true');
  const incoming=[];
  for(let p=0;p<=4;p++)for(let q=0;q<=4;q++){
   const [x,y]=point(p,q),seed=(p*71+q*137+p*q*29)%293;
   const cell=document.createElement('div');cell.className='formation-cell';cell.style.left=(x-34)+'px';cell.style.top=(y-19)+'px';cell.dataset.p=p;cell.dataset.q=q;
   cell.innerHTML=`<div class="formation-card formation-k">${math(`K^{${p},${q}}`)}</div><div class="formation-card formation-z">${math(`\\pi_${p}(Z_{${r}}^{${p},${q}})`)}</div><div class="formation-brackets"><span class="formation-left">[</span><span class="formation-right">]<sub>${math(String(r))}</sub></span></div><div class="formation-card formation-e">${math(`E_{${r}}^{${p},${q}}`)}</div>`;
   layer.append(cell);const k=cell.querySelector('.formation-k'),z=cell.querySelector('.formation-z'),brackets=cell.querySelector('.formation-brackets'),e=cell.querySelector('.formation-e');
   const height=95+seed*.68,duration=960+(seed%163)*5,delay=2050+(seed%131)*4;
   cell.dataset.dropHeight=height;cell.dataset.dropDuration=duration;
   incoming.push({k,z,brackets,e,height,duration,delay});
  }
  host.append(layer);
  // The initial wait shows the source K, never a premature E page.
  base.forEach(el=>animate(el,[{opacity:getComputedStyle(el).opacity},{opacity:0}],{duration:0}));
  for(const {z,brackets,e}of incoming){z.style.opacity=brackets.style.opacity=e.style.opacity='0';}
  prepared={r,incoming};
 }
 async function play(r){
  if(visualMotion().reduced)return;
  if(!prepared||prepared.r!==r)prepare(r);
  const run=serial;running=true;const {incoming}=prepared;

  for(const {k,z,brackets,e,height,duration,delay}of incoming){
   animate(z,[{opacity:0,transform:'scale(.24)'},{opacity:1,transform:'scale(.34)'}],{delay:320,duration:360});
   animate(z,[{transform:'scale(.34)'},{transform:'scale(1)'}],{delay:880,duration:500,fill:'forwards'});
   animate(k,[{opacity:1},{opacity:0}],{delay:1000,duration:380,fill:'forwards'});
   animate(brackets,[{opacity:0},{opacity:.9}],{delay:1450,duration:300});
   animate(e,[{opacity:0,transform:`translateY(${-height}px)`},{opacity:1,offset:.16},{opacity:1,transform:'translateY(0)'}],{delay,duration,easing:'cubic-bezier(.26,.56,.2,1)'});
   animate(z,[{opacity:1},{opacity:0}],{delay:delay+duration-180,duration:180,fill:'forwards'});
   animate(brackets,[{opacity:.9},{opacity:0}],{delay:delay+duration-120,duration:220,fill:'forwards'});
  }
  window.spectralFormation={r,phase:'project-then-quotient',count:25,heights:incoming.map(x=>x.height),durations:incoming.map(x=>x.duration)};
  await Promise.all(animations.map(a=>a.finished.catch(()=>{})));if(run!==serial)return;
  const reveal=base.map(el=>{const original=animations.find(a=>a.effect?.target===el)?.effect.getKeyframes()[0].opacity??1;return animate(el,[{opacity:0},{opacity:original}],{duration:240});});
  const fade=animate(layer,[{opacity:1},{opacity:0}],{duration:240});await Promise.all([...reveal,fade].map(a=>a.finished.catch(()=>{})));if(run!==serial)return;
  animations.forEach(a=>a.cancel());animations=[];base=[];layer.remove();layer=null;prepared=null;running=false;window.spectralFormation.phase='complete';
 }
 return {prepare,play,clear,isPlaying:()=>running};
}
