// Reconcile mathematical diagrams without replacing live visual elements.
// State changes preserve DOM identity so CSS transitions can be interrupted smoothly.
import {visualMotion} from './visual-style.js?v=41';
export function syncGraphChildren(target,source){
 if(target.innerHTML===source.innerHTML)return;
 if(target.id==='diagram-terms'){
  for(const next of [...source.children]){
   const old=target.querySelector(`[data-p="${next.dataset.p}"][data-q="${next.dataset.q}"]`);
   if(!old){target.append(next);continue;}
   for(const attr of [...old.attributes])if(!next.hasAttribute(attr.name))old.removeAttribute(attr.name);
   for(const attr of [...next.attributes])old.setAttribute(attr.name,attr.value);
   if(old.querySelector('.math-anchor')?.dataset.tex!==next.querySelector('.math-anchor')?.dataset.tex){
    const label=next.querySelector('.math-anchor');old.querySelector('.math-anchor').replaceWith(label);fadeGraphAddition(label);
   }
  }
 }else{
  const key=el=>{if(target.id==='diagram-overlays')return el.tagName+':'+[...el.classList].filter(c=>c!=='concept-active').join(' ');const shape=el.matches('path,polygon,rect,foreignObject')?el:el.querySelector('path,polygon,rect,foreignObject');return el.tagName+':'+(shape?[shape.tagName,shape.getAttribute('d'),shape.getAttribute('points'),shape.getAttribute('x'),shape.getAttribute('y')].join(':'):el.outerHTML);};
  const existing=new Map([...target.children].map(el=>[key(el),el]));let cursor=target.firstElementChild;
  for(const next of [...source.children]){
   const k=key(next),old=existing.get(k);let el=old||next;
   if(old){existing.delete(k);if(old.outerHTML!==next.outerHTML){patchGraphElement(old,next);}}
   if(el!==cursor)target.insertBefore(el,cursor);cursor=el.nextElementSibling;
   if(!old)fadeGraphAddition(el);
  }
  for(const el of existing.values())el.remove();
 }
}
function patchGraphElement(old,next){
 for(const attr of [...old.attributes])if(!next.hasAttribute(attr.name))old.removeAttribute(attr.name);
 for(const attr of [...next.attributes])if(old.getAttribute(attr.name)!==attr.value)old.setAttribute(attr.name,attr.value);
 const children=[...old.childNodes],wanted=[...next.childNodes];
 wanted.forEach((child,i)=>{
  const current=children[i];
  if(!current){old.append(child);return;}
  if(current.nodeType!==child.nodeType||current.nodeName!==child.nodeName){current.replaceWith(child);return;}
  if(child.nodeType===Node.ELEMENT_NODE)patchGraphElement(current,child);
  else if(current.textContent!==child.textContent)current.textContent=child.textContent;
 });
 children.slice(wanted.length).forEach(child=>child.remove());
}
export function restingOpacity(el){
 const style=getComputedStyle(el),transition=el.getAnimations().find(a=>a.transitionProperty==='opacity');
 return transition?.effect.getKeyframes().at(-1)?.opacity??style.opacity;
}
export function fadeGraphAddition(el){
 queueMicrotask(()=>{
  if(!el.isConnected||matchMedia('(prefers-reduced-motion: reduce)').matches||el.getAnimations({subtree:true}).some(a=>!a.transitionProperty))return;
  el.animate([{opacity:0},{opacity:restingOpacity(el)}],{duration:visualMotion().enter,easing:visualMotion().easing});
 });
}
