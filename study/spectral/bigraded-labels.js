import {replaceMathContent} from './math-transitions.js?v=64';
import {visualMotion} from './visual-style.js?v=41';
// Reserve identical symbol, superscript and subscript slots in K and E_0.
// Only K/E and the presence of the 0 change; MathML keeps the exact notation.
export function replaceBigradedLabel(host,tex,math){
 const match=/^(K|E_0)\^\{([^}]+)\}$/.exec(tex);
 if(!match){replaceMathContent(host,math(tex));return;}
 const isPage=match[1]==='E_0',holder=document.createElement('div');
 holder.innerHTML=math(`E_0^{${match[2]}}`);
 const glyph=holder.querySelector('.katex-html .base > .mord > .mathnormal');
 glyph.classList.add('term-base-symbol');glyph.textContent=isPage?'E':'K';
 const sub=holder.querySelector('.msupsub .vlist > span');sub.classList.add('term-page-index');sub.style.opacity=isPage?'1':'0';
 if(!isPage){const semantic=document.createElement('div');semantic.innerHTML=math(tex);holder.querySelector('.katex-mathml').replaceWith(semantic.querySelector('.katex-mathml'));}
 const oldSub=host.querySelector('.term-page-index'),from=oldSub?getComputedStyle(oldSub).opacity:null;
 replaceMathContent(host,holder.innerHTML);
 const motion=visualMotion(),to=isPage?'1':'0';
 if(from!==null&&from!==to&&!motion.reduced)host.querySelector('.term-page-index').animate([{opacity:from},{opacity:to}],{duration:motion.emphasis,easing:motion.easing});
}
