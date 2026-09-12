// Animate rendered mathematical tokens while exposing only the current MathML.
// Degrees stay integers: changed tokens crossfade; they are never interpolated.
import {visualMotion} from './visual-style.js?v=40';
const previousMarkup=new WeakMap();
const visualRoots=host=>[...host.querySelectorAll('.katex-html')].filter(el=>!el.closest('[data-math-old]'));
function leaves(root){
 return [...root.querySelectorAll('span')].filter(el=>
  !el.closest('[data-math-old],[data-math-current]')&&
  (el.dataset.mathText!==undefined||!el.childElementCount&&el.textContent.trim()));
}
function snapshot(el){
 const copy=el.cloneNode(true),source=[el,...el.querySelectorAll('*')],clones=[copy,...copy.querySelectorAll('*')];
 source.forEach((node,i)=>{if(node.hasAttribute('data-math-old')||node.hasAttribute('data-math-current'))clones[i].style.opacity=getComputedStyle(node).opacity;});
 return copy.innerHTML;
}
function blend(el,oldHTML,newHTML,motion,text=null){
 el.classList.add('math-swap');if(text!==null)el.dataset.mathText=text;
 const old=document.createElement('span'),current=document.createElement('span');
 old.dataset.mathOld='';old.setAttribute('aria-hidden','true');old.innerHTML=oldHTML;
 current.dataset.mathCurrent='';current.innerHTML=newHTML;el.replaceChildren(old,current);
 const options={duration:motion.emphasis,easing:motion.easing,fill:'both'};
 const fadeOut=old.animate([{opacity:1},{opacity:0}],options),fadeIn=current.animate([{opacity:0},{opacity:1}],options);
 fadeIn.finished.then(()=>{
  if(el.contains(current)){el.innerHTML=newHTML;el.classList.remove('math-swap');delete el.dataset.mathText;}
  fadeIn.cancel();fadeOut.cancel();
 },()=>{});
}
export function replaceMathContent(host,markup,{animate=true}={}){
 const previous=previousMarkup.get(host);
 if(previous?.markup===markup&&previous.firstChild===host.firstChild)return;
 const motion=visualMotion();
 const old=visualRoots(host).map(root=>({
  root,html:snapshot(root),tex:root.parentElement.querySelector('annotation')?.textContent,
  tokens:leaves(root).map(el=>({el,text:el.dataset.mathText??el.textContent,classes:el.className.replace(/\s*math-swap/g,''),html:snapshot(el)}))
 }));
 host.innerHTML=markup;
 previousMarkup.set(host,{markup,firstChild:host.firstChild});
 if(!animate||motion.reduced||!old.length)return;
 visualRoots(host).forEach((root,i)=>{
  const before=old[i];if(!before)return;
  const tex=root.parentElement.querySelector('annotation')?.textContent;
  const next=leaves(root);
  // C^n and Tot^n share fixed single-digit KaTeX metrics. Keep the live
  // typeset skeleton: only the two numerals crossfade. In particular, never
  // replace C, :=, Tot, K or the superscript baseline at a degree boundary.
  const totalDegree=source=>/^C\^\{[0-9]\}:=\\operatorname\{Tot\}\^\{[0-9]\}K$/.test(source||'');
  if(totalDegree(before.tex)&&totalDegree(tex)&&next.length===before.tokens.length){
   root.replaceWith(before.root);
   next.forEach((el,j)=>{const token=before.tokens[j];if(el.textContent!==token.text)blend(token.el,token.html,el.innerHTML,motion,el.textContent);});
   return;
  }
  if(before.tex===tex)return;
  if(next.length===before.tokens.length&&next.every((el,j)=>el.className===before.tokens[j].classes)){
   next.forEach((el,j)=>{const token=before.tokens[j];if(el.textContent!==token.text)blend(el,token.html,el.innerHTML,motion,el.textContent);});
  }else blend(root,before.html,root.innerHTML,motion);
 });
}
