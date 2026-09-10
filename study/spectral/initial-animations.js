// One entrance timeline for the fixed double-complex diagram. Nothing here
// advances the notebook or changes mathematical state / lattice coordinates.
import {visualMotion} from './visual-style.js?v=41';

export function createInitialAnimations({diagram}) {
 const reduced=matchMedia('(prefers-reduced-motion:reduce)');
 const running=new Set();
 let key=null,previous=-1,openingEnd=0,directionEnd=0,serial=0;
 const all=selector=>[...diagram.querySelectorAll(selector)];
 const play=(el,frames,options,id)=>{
  if(!el)return;
  const animation=el.animate(frames,{easing:visualMotion().easing,fill:'backwards',...options});
  animation.id=`initial-${id}`;running.add(animation);
  animation.finished.then(()=>{running.delete(animation);},()=>{running.delete(animation);});
  return animation;
 };
 const settle=()=>{
  // Sample all effects before cancelling any: labels and SVG tiles must settle
  // together, including a rapid exit during their delayed pop-in.
  const targets=[...new Set([...running].map(a=>a.effect?.target).filter(el=>el?.isConnected))];
  const snapshots=targets.map(el=>{const s=getComputedStyle(el);return {el,opacity:s.opacity,transform:s.transform,transformOrigin:s.transformOrigin};});
  [...running].forEach(a=>a.cancel());running.clear();
  if(reduced.matches)return;
  snapshots.forEach(({el,opacity,transform,transformOrigin})=>{
   const rest=getComputedStyle(el);
   if(opacity===rest.opacity&&transform===rest.transform)return;
   play(el,[{opacity,transform,transformOrigin},{opacity:rest.opacity,transform:rest.transform,transformOrigin}],{duration:visualMotion().exit},'settle');
  });
 };
 function open() {
  const motion=visualMotion(),{axis,pop,stagger}=motion.initial;
  const origin=diagram.querySelector('.coordinate-axes').dataset;
  const transformOrigin=`${origin.originX}px ${origin.originY}px`;
  openingEnd=performance.now()+axis+8*stagger+pop;
  directionEnd=openingEnd;
  for(const [name,scale] of [['p','scaleX'],['q','scaleY']]){
   play(diagram.querySelector(`#${name}-axis`),[
    {transform:`${scale}(0)`,transformOrigin},{transform:`${scale}(1)`,transformOrigin}
   ],{duration:axis},`axis-${name}`);
  }
  all('.axis-name,.grid').forEach((el,i)=>play(el,[{opacity:0},{opacity:getComputedStyle(el).opacity}],{duration:axis*.6,delay:axis*.3},`frame-${i}`));
  all('.axis-tick').forEach((el,i)=>{
   const delay=axis*.2+Number(el.dataset.value)*stagger;
   play(el,[{opacity:0},{opacity:1,offset:.32},{opacity:1,offset:.76},{opacity:0}],{duration:axis+pop*.25-delay,delay},`tick-${i}`);
  });
  const tileDelays=new Map();
  all('.node').forEach(node=>{
   const p=Number(node.dataset.p),q=Number(node.dataset.q),anchor=node.querySelector('.math-anchor');
   if(!anchor)return;
   const {x,y,width,height}=anchor.dataset,cx=Number(x)+Number(width)/2,cy=Number(y)+Number(height)/2;
   const label=all('.term-label').find(el=>el.dataset.key===[x,y,width,height].join(':'));
   const delay=axis+(p+q)*stagger;
   tileDelays.set(`${cx},${cy}`,delay);
   for(const [el,origin] of [[node,`${cx}px ${cy}px`],[label,'50% 50%']]){
    if(!el)continue;
    play(el,[
     {opacity:0,transform:'scale(.24)',transformOrigin:origin},
     {opacity:1,transform:'scale(1.065)',transformOrigin:origin,offset:.72},
     {opacity:1,transform:'scale(1)',transformOrigin:origin}
    ],{duration:pop,delay},`term-${p}-${q}`);
   }
  });
  // Boundary ellipses appear only after the last K tile has finished popping.
  all('.extent-label').forEach((el,i)=>play(el,[{opacity:0},{opacity:1}],{duration:motion.enter,delay:axis+8*stagger+pop},`extent-${i}`));
  // Cut an axis behind a tile only as that tile appears, never in the empty frame.
  all('#coordinate-axis-mask rect[fill="black"]').forEach((el,i)=>{
   const x=Number(el.getAttribute('x'))+Number(el.getAttribute('width'))/2;
   const y=Number(el.getAttribute('y'))+Number(el.getAttribute('height'))/2;
   play(el,[{opacity:0},{opacity:1}],{duration:pop*.6,delay:tileDelays.get(`${x},${y}`)??axis},`mask-${i}`);
  });
 }
 function revealDirection(name) {
  const {initial,easing}=visualMotion(),horizontal=name==='p',concept=horizontal?'delta1':'delta2';
  const delay=Math.max(initial.axisExit,openingEnd-performance.now(),directionEnd-performance.now());
  directionEnd=performance.now()+delay+initial.arrow;
  all(`.arrow.${horizontal?'h':'v'},.continuation[data-concept="${concept}"]`).forEach((el,i)=>{
   const start=el.getAttribute('d').match(/^M\s*([-\d.]+)[ ,]+([-\d.]+)/);
   if(!start)return;
   const transformOrigin=`${start[1]}px ${start[2]}px`,scale=horizontal?'scaleX':'scaleY';
   play(el,[{transform:`${scale}(0)`,transformOrigin},{transform:`${scale}(1)`,transformOrigin}],{duration:initial.arrow,delay,easing},`arrow-${name}-${i}`);
  });
  // Fade inside the label wrapper: concept opacity stays free to change when
  // the reader introduces the other differential during this animation.
  all(`.map-label[data-map-concept="${concept}"]`).forEach((el,i)=>play(el.firstElementChild||el,[{opacity:0},{opacity:1}],{duration:initial.arrow*.6,delay:delay+initial.arrow*.4},`label-${name}-${i}`));
 }
 function sync({active,step,seenH,seenV}) {
  const next=active?`initial:${step}`:'outside';
  if(next===key)return;
  const wasActive=key?.startsWith('initial:'),old=previous;
  key=next;previous=active?step:-1;
  const continuing=active&&wasActive&&old>=0&&old<step&&step<=2;
  if(!continuing){settle();openingEnd=directionEnd=0;}
  diagram.classList.toggle('initial-hide-p',active&&seenH);
  diagram.classList.toggle('initial-hide-q',active&&seenV);
  if(!active||reduced.matches){openingEnd=directionEnd=0;publish();return;}
  if(step===0&&(!wasActive||old<0)){serial++;open();}
  else if(step===1&&(!wasActive||old<1)){revealDirection('p');}
  else if(step===2&&(!wasActive||old<2)){revealDirection('q');}
  publish();
 }
 function publish(){window.spectralEntrance={key,openingSerial:serial,reduced:reduced.matches};}
 reduced.addEventListener('change',()=>{if(reduced.matches){[...running].forEach(a=>a.cancel());running.clear();openingEnd=directionEnd=0;}publish();});
 return {sync};
}
