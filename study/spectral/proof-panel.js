// Concise exposition on the page; complete derivations in one accessible dialog.
// Opening a proof never navigates the notebook or changes the diagram state.
const proofs=new Map();let dialog=null;
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function ensureDialog(){
 if(dialog)return dialog;
 dialog=document.createElement('dialog');dialog.id='proofDetailDialog';dialog.setAttribute('aria-labelledby','proofDetailTitle');
 dialog.innerHTML='<header class="proof-detail-header"><h2 id="proofDetailTitle"></h2><button type="button" data-close-proof>×</button></header><div class="proof-detail-content"></div>';
 document.body.append(dialog);
 dialog.querySelector('[data-close-proof]').addEventListener('click',()=>dialog.close());
 dialog.addEventListener('click',e=>{if(e.target===dialog){const r=dialog.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)dialog.close();}});
 dialog.addEventListener('close',()=>{dialog.querySelector('.proof-detail-content').innerHTML='';});
 return dialog;
}
document.addEventListener('click',e=>{
 const trigger=e.target.closest('[data-proof-detail]');if(!trigger)return;
 const proof=proofs.get(trigger.dataset.proofDetail);if(!proof)return;
 e.preventDefault();e.stopImmediatePropagation();const panel=ensureDialog();
 panel.querySelector('h2').innerHTML=proof.titleMarkup;
 const close=panel.querySelector('[data-close-proof]');close.setAttribute('aria-label',proof.english?'Close proof':'关闭证明');
 const body=panel.querySelector('.proof-detail-content');body.innerHTML=proof.details;body.scrollTop=0;
 if(!panel.open)panel.showModal();
 if(!matchMedia('(prefers-reduced-motion:reduce)').matches)panel.animate([{opacity:0},{opacity:1}],{duration:180,easing:'ease-out'});
},true);
export function proofPanel({key,title,titleMath='',formulas,note='',details,math,language}){
 const english=language()==='en';proofs.set(key,{titleMarkup:esc(title)+(titleMath?' '+math(titleMath):''),details,english});
 const hint=english?'Click a formula for the proof':'点击公式查看证明';
 return `<div class="exposition-summary">${formulas.map(f=>`<button type="button" class="proof-formula operation-equation" data-proof-detail="${esc(key)}" aria-haspopup="dialog" title="${hint}">${math(f,true)}</button>`).join('')}${note?`<p class="operation-note">${note}</p>`:''}<button type="button" class="proof-detail-link" data-proof-detail="${esc(key)}" aria-haspopup="dialog">${english?'Proof and derivation':'证明与推导'} <span aria-hidden="true">↗</span></button></div>`;
}
export function proofSections(entries,{math,title=e=>e.name,note=e=>e.note}={}){
 return entries.map(e=>`<section class="proof-detail-section"><h3>${esc(title(e))}</h3>${e.f.map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}${note(e)?`<p>${note(e)}</p>`:''}</section>`).join('');
}
