// Shared semantic marks: abbreviations are stable; accessible names follow language.
export const statementKinds={T:['Thm','定理','Theorem'],P:['Pro','命题','Proposition'],L:['Lem','引理','Lemma'],D:['Def','定义','Definition'],E:['Ex.','例子','Example'],C:['Cor','推论','Corollary']};
export function statementMark(kind,english=false){
 const entry=statementKinds[kind];if(!entry)return '';
 const [text,zh,en]=entry,name=english?en:zh;
 return `<span class="statement-mark" data-statement-kind="${kind}" role="img" aria-label="${name}" title="${name}"><span aria-hidden="true">${text}</span></span>`;
}
export function stripStatementKind(title){return title.replace(/^(?:Theorem|Proposition|Lemma|Definition|Example|Corollary|Property|定理|命题|引理|定义|例子|推论|性质)\s*[:：]\s*/,'');}
export function markedTitle(title,english=false){
 const esc=x=>x.replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
 const match=title.match(/^(\d+\.\d+\s+)?(Theorem|Proposition|Lemma|Definition|Example|Corollary|定理|命题|引理|定义|例子|推论)\s*[:：.]?\s*/);
 if(!match)return esc(title);
 const kind=Object.keys(statementKinds).find(k=>statementKinds[k].slice(1).includes(match[2]));
 return esc(match[1]||'')+statementMark(kind,english)+' '+esc(title.slice(match[0].length));
}
export function createStatementMarkSettings({language}){
 const root=document.documentElement,key='spectral-statement-marks',choices={bare:['A · 无框','A · Bare'],circle:['B · 圆环','B · Ring'],square:['C · 方框','C · Framed']};
 let current='square';try{const saved=localStorage.getItem(key);if(choices[saved])current=saved;}catch{}
 const group=document.createElement('fieldset');group.className='statement-mark-setting';
 group.innerHTML='<legend></legend><div class="statement-mark-choices">'+Object.entries(choices).map(([value])=>`<label data-mark-choice="${value}"><input type="radio" name="statementMarkStyle" value="${value}"><span class="mark-choice-name"></span><span class="mark-choice-sample" aria-hidden="true">Pro</span></label>`).join('')+'</div><div class="statement-mark-legend"></div>';
 document.querySelector('.panel-style-setting').after(group);
 function sync(){const en=language()==='en';group.querySelector('legend').textContent=en?'Statement marks':'数学陈述字标';for(const el of group.querySelectorAll('[data-mark-choice]')){el.querySelector('.mark-choice-name').textContent=choices[el.dataset.markChoice][en?1:0];el.querySelector('input').checked=el.dataset.markChoice===current;}group.querySelector('.statement-mark-legend').innerHTML=['T','P','L','D','E'].map(k=>`<span>${statementMark(k,en)} ${statementKinds[k][en?2:1]}</span>`).join('');}
 function set(value){if(!choices[value])return;current=value;root.dataset.markStyle=value;try{localStorage.setItem(key,value);}catch{}sync();}
 root.dataset.markStyle=current;sync();group.addEventListener('change',e=>{if(e.target.matches('[name="statementMarkStyle"]'))set(e.target.value);});
 document.querySelector('#motionReset').addEventListener('click',()=>set('square'));
 return {sync,set};
}
