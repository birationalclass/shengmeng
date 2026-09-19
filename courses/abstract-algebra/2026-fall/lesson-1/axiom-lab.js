/* Conditions refer to ONE specified e in a nonempty set with a closed operation. */
(()=>{
'use strict';
const keys=['A','L','R','I','J'];
function inspect(table,e=0){const n=table.length,ids=Array.from({length:n},(_,i)=>i);let witness=null;
 for(const a of ids)for(const b of ids)for(const c of ids)if(table[table[a][b]][c]!==table[a][table[b][c]]&&!witness)witness=[a,b,c];
 const facts={A:!witness,L:ids.every(a=>table[e][a]===a),R:ids.every(a=>table[a][e]===a),I:ids.every(a=>ids.some(b=>table[b][a]===e)),J:ids.every(a=>ids.some(b=>table[a][b]===e))};
 const identity=ids.find(u=>ids.every(a=>table[u][a]===a&&table[a][u]===a));
 return{facts,witness,identity,group:!witness&&identity!==undefined&&ids.every(a=>ids.some(b=>table[a][b]===identity&&table[b][a]===identity))};
}
function implies(s){return !!(s.A&&((s.L&&s.I)||(s.R&&s.J)));}
const tables2=Array.from({length:16},(_,bits)=>[[bits&1,(bits>>1)&1],[(bits>>2)&1,(bits>>3)&1]]);
function solve(selected){if(implies(selected))return{group:true,side:selected.L&&selected.I?'left':'right'};
 const table=tables2.find(t=>{const f=inspect(t);return !f.group&&keys.every(k=>!selected[k]||f.facts[k]);})||[[0,1,2],[1,0,0],[2,0,0]];
 return{group:false,table,...inspect(table)};
}
window.GroupAxiomLab={keys,inspect,implies,solve,render(scene){
 let selected={A:true,L:true,R:false,I:true,J:false};
 const en=()=>window.CourseLanguage?.language==='en',t=(zh,english)=>en()?english:zh;
 const names={A:['结合律','Associativity'],L:['左单位元','Left identity'],R:['右单位元','Right identity'],I:['每个元素有左逆','Left inverses for all'],J:['每个元素有右逆','Right inverses for all']};
 const equations={A:'(ab)c = a(bc)',L:'ea = a',R:'ae = a',I:'∀a ∃b: ba = e',J:'∀a ∃c: ac = e'};
 const left=[['任取 a。由左逆条件取 b、c，使 ba=e、cb=e。','For any a choose b,c with ba=e and cb=e.'],['a = ea = (cb)a = c(ba) = ce。','a = ea = (cb)a = c(ba) = ce.'],['ab = (ce)b = c(eb) = cb = e。左逆 b 也是右逆。','ab = (ce)b = c(eb) = cb = e. Thus b is also a right inverse.'],['ae = a(ba) = (ab)a = ea = a。e 也是右单位元。','ae = a(ba) = (ab)a = ea = a. Thus e is also a right identity.']];
 const right=[['任取 a。由右逆条件取 b、c，使 ab=e、bc=e。','For any a choose b,c with ab=e and bc=e.'],['a = ae = a(bc) = (ab)c = ec。','a = ae = a(bc) = (ab)c = ec.'],['ba = b(ec) = (be)c = bc = e。右逆 b 也是左逆。','ba = b(ec) = (be)c = bc = e. Thus b is also a left inverse.'],['ea = (ab)a = a(ba) = ae = a。e 也是左单位元。','ea = (ab)a = a(ba) = ae = a. Thus e is also a left identity.']];
 function draw(){const result=solve(selected),labels=['e','a','b'],f=x=>labels[x];
 scene.innerHTML=`<div class="axiom-lab"><p class="axiom-premise">${t('固定：非空集合 G、封闭运算 G×G→G，以及同一个候选元素 e∈G。未勾选的条件表示“不要求”，并非要求它不成立。','Fix a nonempty G, a closed operation G×G→G, and one candidate e∈G. Unchecked conditions are not assumed; they are not required to fail.')}</p><fieldset class="axiom-choices"><legend>${t('勾选假设','Choose assumptions')}</legend>${keys.map(k=>`<label><input type="checkbox" data-axiom="${k}" ${selected[k]?'checked':''}><span><b>${t(...names[k])}</b><small>${equations[k]}</small></span></label>`).join('')}</fieldset><div class="axiom-verdict ${result.group?'is-group':'is-counterexample'}" role="status"><b>${result.group?t('能推出群 · 等价定义','Implies a group · equivalent definition'):t('不能推出群','Does not imply a group')}</b><p>${t('完整判据：结合律，且“左单位＋左逆”或“右单位＋右逆”至少一组成立。','Exact criterion: associativity and at least one of (left identity + left inverses) or (right identity + right inverses).')}</p></div><div class="axiom-result"></div><details class="axiom-all"><summary>${t('查看全部 32 种条件组合','All 32 combinations')}</summary><div class="axiom-combinations">${Array.from({length:32},(_,mask)=>{const s=Object.fromEntries(keys.map((k,i)=>[k,!!(mask&(1<<i))]));return `<button type="button" data-mask="${mask}" aria-pressed="${keys.every(k=>s[k]===selected[k])}"><span>${keys.filter(k=>s[k]).map(k=>t(...names[k])).join(' + ')||t('无额外条件','No extra conditions')}</span><b>${implies(s)?'✓':'×'}</b></button>`}).join('')}</div></details></div>`;
 const out=scene.querySelector('.axiom-result');
 if(result.group){out.innerHTML=`<h3>${t('简化证明','Short proof')}</h3><p>${t('群必满足已选条件。反过来，只用以下同侧条件即可，其余勾选条件是多余的。','Every group satisfies the selected assumptions. Conversely, the following same-side conditions suffice; any additional selections are redundant.')}</p><ol>${(result.side==='left'?left:right).map(pair=>`<li>${t(...pair)}</li>`).join('')}</ol><p>${t('关键：逆元条件针对每个元素，包括刚选出的 b；没有使用消去律，也没有假设交换律。','The inverse assumption applies to every element, including b. Neither cancellation nor commutativity is assumed.')}</p>`;}
 else{const n=result.table.length,ids=Array.from({length:n},(_,i)=>i),table=result.table;let failure;
 if(result.witness){const[a,b,c]=result.witness;failure=`(${f(a)}${f(b)})${f(c)} = ${f(table[table[a][b]][c])} ≠ ${f(table[a][table[b][c]])} = ${f(a)}(${f(b)}${f(c)})`;}
 else if(result.identity===undefined)failure=t('没有任何双侧单位元（逐行、逐列检查表格即可），所以不是群。','No element is a two-sided identity (check every row and column), so this is not a group.');
 else{const a=ids.find(a=>!ids.some(b=>table[a][b]===result.identity&&table[b][a]===result.identity));failure=t(`唯一单位元为 ${f(result.identity)}，但 ${f(a)} 没有双侧逆元。`,`The unique identity is ${f(result.identity)}, but ${f(a)} has no two-sided inverse.`);}
 const code=JSON.stringify(table);
 const associativeProof=code==='[[0,0],[0,0]]'?t('任意 xy=e，所以 (xy)z=e=x(yz)。','Every product is e, so (xy)z=e=x(yz).'):code==='[[0,0],[1,1]]'?t('运算 xy=x；因此 (xy)z=x=x(yz)。','Here xy=x, hence (xy)z=x=x(yz).'):code==='[[0,1],[0,1]]'?t('运算 xy=y；因此 (xy)z=z=x(yz)。','Here xy=y, hence (xy)z=z=x(yz).'):code==='[[0,1],[1,1]]'?t('e 为单位元，a 为吸收元。三个因子全为 e 时结果为 e，否则结果恒为 a，与括号无关。','e is an identity and a is absorbing. Any triple gives e if all factors are e, and a otherwise, independently of bracketing.'):t('直接检查全部三元组，两种加括号方式相等。','Check that both bracketings agree for every triple.');
 const checks=keys.filter(k=>selected[k]).map(k=>{
 let detail=k==='A'?associativeProof:k==='L'?ids.map(a=>`e·${f(a)}=${f(a)}`).join('，'):k==='R'?ids.map(a=>`${f(a)}·e=${f(a)}`).join('，'):ids.map(a=>{const b=ids.find(b=>(k==='I'?table[b][a]:table[a][b])===0);return k==='I'?`${f(b)}·${f(a)}=e`:`${f(a)}·${f(b)}=e`;}).join('，');return `<li><b>${t(...names[k])}：</b>${detail}</li>`;}).join('');
 out.innerHTML=`<h3>${t('最小反例','Smallest counterexample')} · ${n} ${t('个元素','elements')}</h3><p>G = {${ids.map(f).join(', ')}}；${t('行元素乘列元素','row times column')}</p><table class="axiom-table"><thead><tr><th>·</th>${ids.map(a=>`<th>${f(a)}</th>`).join('')}</tr></thead><tbody>${table.map((row,a)=>`<tr><th>${f(a)}</th>${row.map(x=>`<td>${f(x)}</td>`).join('')}</tr>`).join('')}</tbody></table><h4>${t('为什么满足所选条件','Why the selected assumptions hold')}</h4><ul>${checks||`<li>${t('运算表所有结果均在 G 内，满足非空与封闭。','The nonempty table is closed on G.')}</li>`}</ul><h4>${t('为什么不是群','Why it is not a group')}</h4><p class="axiom-witness">${failure}</p><p class="axiom-minimal">${n===2?t('最小性：一个元素的封闭运算必为平凡群，因此两个元素已经最小。','Minimality: every one-element closed operation is the trivial group.'):t('最小性：单元素必为群；两元素有双侧单位元 e 时，若另一个元素 a 有任一侧逆元，只能 aa=e，运算表被迫是二阶循环群。因此至少需要三个元素。','Minimality: one element gives a group. With two elements and a two-sided identity e, any one-sided inverse for the other element a forces aa=e, giving C₂. Hence three elements are necessary.')}</p>`;
 }
 scene.querySelectorAll('[data-axiom]').forEach(input=>input.onchange=()=>{const key=input.dataset.axiom;selected[key]=input.checked;draw();scene.querySelector(`[data-axiom="${key}"]`).focus({preventScroll:true});});
 scene.querySelectorAll('[data-mask]').forEach(button=>button.onclick=()=>{const mask=+button.dataset.mask;selected=Object.fromEntries(keys.map((k,i)=>[k,!!(mask&(1<<i))]));draw();});
 }
 const rerender=()=>draw();window.addEventListener('course-language',rerender);window.addEventListener('lesson-topic',()=>window.removeEventListener('course-language',rerender),{once:true});draw();
}};
})();
