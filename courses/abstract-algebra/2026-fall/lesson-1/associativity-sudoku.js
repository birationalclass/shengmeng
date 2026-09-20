/* A Latin-square puzzle. No 3-by-3 Sudoku block constraint is imposed. */
(()=>{
  'use strict';
  const levels=new Map();
  function level(n){
    if(levels.has(n))return levels.get(n);
    const pool=Array.from({length:n-1},(_,i)=>i+1);let seed=n*7919;
    for(let i=pool.length-1;i>0;i--){seed=(seed*1664525+1013904223)>>>0;const j=seed%(i+1);[pool[i],pool[j]]=[pool[j],pool[i]];}
    const labels=[n,...pool],codes=Object.fromEntries(labels.map((v,i)=>[v,i]));
    let generators=[1],name=`C${n}`,raw=(a,b)=>(a+b)%n,kind='cyclic';
    if(n===4){generators=[1,2];name='C₂ × C₂';kind='klein';raw=(a,b)=>a^b;}
    if(n===6||n===8){const k=n/2;generators=[1,k];name=n===6?'S₃':'D₄';kind='dihedral';raw=(a,b)=>((a%k+(a<k?1:-1)*(b%k)+k)%k)+k*((Math.floor(a/k)+Math.floor(b/k))%2);}
    if(n===9){generators=[1,3];name='C₃ × C₃';kind='plane';raw=(a,b)=>(a%3+b%3)%3+3*((Math.floor(a/3)+Math.floor(b/3))%3);}
    const multiply=(a,b)=>labels[raw(codes[a],codes[b])],gens=generators.map(g=>labels[g]);
    // Known generator rows determine a word reaching every element from e.
    const reached=new Map([[n,[]]]),queue=[n];
    while(queue.length){const b=queue.shift();for(const g of gens){const d=multiply(g,b);if(!reached.has(d)){reached.set(d,[g,...reached.get(b)]);queue.push(d);}}}
    if(reached.size!==n)throw new Error('Generators do not span this level');
    const result={n,identity:n,labels,gens,name,kind,multiply,words:reached};levels.set(n,result);return result;
  }
  const product=(a,b,n=9)=>level(n).multiply(a,b);
  const puzzles=new Map();
  function forced(values,preferred){
    const n=Math.sqrt(values.length),at=(a,b)=>(a-1)*n+b-1;let fallback=null;
    const keep=h=>{if(!fallback)fallback=h;return h.target===preferred;};
    for(let axis=0;axis<2;axis++)for(let line=0;line<n;line++){
      const cells=Array.from({length:n},(_,j)=>axis?j*n+line:line*n+j),empty=cells.filter(i=>!values[i]);
      if(empty.length!==1)continue;
      const missing=Array.from({length:n},(_,i)=>i+1).filter(v=>!cells.some(i=>values[i]===v));
      if(missing.length!==1)continue;
      const h={latin:true,axis,line,target:empty[0],value:missing[0],cells};if(keep(h))return h;
    }
    for(let a=1;a<=n;a++)for(let b=1;b<=n;b++)for(let c=1;c<=n;c++){
      const ab=values[at(a,b)],bc=values[at(b,c)];if(!ab||!bc)continue;
      const left=at(ab,c),right=at(a,bc);if(left===right)continue;
      if((!values[left])===(!values[right]))continue;
      const target=values[left]?right:left,value=values[left]||values[right];
      const h={a,b,c,ab,bc,left,right,target,value,cells:[at(a,b),at(b,c),left,right]};if(keep(h))return h;
    }
    return fallback;
  }
  function completeForced(clues){
    const values=[...clues],steps=[];
    while(values.includes(0)){const h=forced(values);if(!h)return null;values[h.target]=h.value;steps.push(h);}
    return {values,steps};
  }
  function puzzle(n){
    if(puzzles.has(n))return puzzles.get(n);
    const full=Array.from({length:n*n},(_,i)=>product(Math.floor(i/n)+1,i%n+1,n));
    const minimum=n===2?3:Math.max(n+1,Math.ceil(n*n*.4));let best=null,bestScore=-Infinity;
    for(let attempt=0;attempt<10;attempt++){
      const clues=[...full],order=Array.from({length:n*n},(_,i)=>i);let seed=n*6151+attempt*7919;
      for(let i=order.length-1;i>0;i--){seed=(seed*1664525+1013904223)>>>0;const j=seed%(i+1);[order[i],order[j]]=[order[j],order[i]];}
      let count=n*n;
      for(const i of order){if(count<=minimum)break;const previous=clues[i];clues[i]=0;const result=completeForced(clues);if(!result||result.values.some((v,k)=>v!==full[k]))clues[i]=previous;else count--;}
      const certificate=completeForced(clues),rowCounts=Array.from({length:n},(_,r)=>clues.slice(r*n,(r+1)*n).filter(Boolean).length),colCounts=Array.from({length:n},(_,c)=>clues.filter((v,i)=>i%n===c&&v).length);
      const spread=[...rowCounts,...colCounts].filter(v=>v>0&&v<n).length,assoc=certificate.steps.filter(h=>!h.latin).length;
      const score=spread*100+Math.min(assoc,5)*5-count;
      if(score>bestScore){bestScore=score;best={clues,certificate:certificate.steps,full,assoc};}
      if(spread===2*n&&(n<4||assoc>0))break;
    }
    puzzles.set(n,best);return best;
  }
  const initial=(n=9)=>[...puzzle(n).clues];
  function inspect(values){
    const N=Math.sqrt(values.length),index=(r,c)=>r*N+c;
    for(let axis=0;axis<2;axis++)for(let a=0;a<N;a++){
      const seen=new Map();
      for(let b=0;b<N;b++){
        const i=axis?index(b,a):index(a,b),v=values[i];if(!v)continue;
        if(seen.has(v))return {kind:'repeat',axis,a,value:v,cells:[seen.get(v),i]};seen.set(v,i);
      }
    }
    let checked=0;
    for(let a=1;a<=N;a++)for(let b=1;b<=N;b++)for(let c=1;c<=N;c++){
      const ab=values[index(a-1,b-1)],bc=values[index(b-1,c-1)];if(!ab||!bc)continue;
      const l=values[index(ab-1,c-1)],r=values[index(a-1,bc-1)];if(!l||!r)continue;
      checked++;if(l!==r)return {kind:'associativity',a,b,c,l,r,cells:[index(a-1,b-1),index(b-1,c-1),index(ab-1,c-1),index(a-1,bc-1)]};
    }
    return {kind:values.every(Boolean)?'complete':'partial',checked,filled:values.filter(Boolean).length};
  }
  const deduction=(values,preferred)=>forced(values,preferred);
  function applySkill(values,kind){
    const n=Math.sqrt(values.length),out=[...values],givens=initial(n),changed=[],conflicts=[];
    if(kind==='identity'){for(let x=1;x<=n;x++)for(const i of [(n-1)*n+x-1,(x-1)*n+n-1]){if(!givens[i]&&out[i]!==x){out[i]=x;changed.push(i);}}}
    if(kind==='inverse'){values.forEach((v,i)=>{if(v!==n)return;const target=(i%n)*n+Math.floor(i/n);if(out[target]&&out[target]!==n)conflicts.push(target);else if(!out[target]&&!givens[target]){out[target]=n;changed.push(target);}});}
    return conflicts.length?{values:[...values],changed:[],conflicts}:{values:out,changed:[...new Set(changed)],conflicts:[]};
  }
  const model={initial,inspect,deduction,product,level,puzzle,completeForced,applySkill};
  if(typeof module!=='undefined'&&module.exports)module.exports=model;
  if(typeof window==='undefined')return;
  window.AssociativitySudokuModel=model;
  let dispose=()=>{};
  window.AssociativitySudoku={render(host,options={}){
    dispose();const abort=new AbortController();dispose=()=>abort.abort();
    let N=options.level||2,values=options.values?[...options.values]:initial(N),selected=values.findIndex(v=>!v),skill='',hint=null,issue=null,message='',proofOpen=false;
    const index=(r,c)=>r*N+c,completed=new Set(options.completed||[]);
    if(selected<0)selected=0;
    const changed=()=>options.onChange?.(N,[...values]);
    const skillLocked=id=>id==='identity'?options.requireIdentityUnlock&&!completed.has(3):id==='inverse'?options.requireInverseUnlock&&!completed.has(5):false;
    const en=()=>window.CourseLanguage?.language==='en',t=(zh,eng)=>en()?eng:zh;
    const unlockNote=id=>id==='identity'?t('通关 3×3 后解锁','Complete 3×3 to unlock'):t('通关第 4 关（5×5）后解锁','Complete level 4 (5×5) to unlock');
    host.innerHTML='<section class="algebra-sudoku"></section>';const root=host.firstElementChild;
    const given=i=>initial(N)[i]!==0;
    function feedback(result){
      if(result.kind==='repeat')return t(`${result.axis?'第 '+(result.a+1)+' 列':'第 '+(result.a+1)+' 行'}重复出现 ${result.value}。`,`${result.axis?'Column':'Row'} ${result.a+1} repeats ${result.value}.`);
      if(result.kind==='associativity')return t(`结合律不成立：(${result.a}·${result.b})·${result.c} = ${result.l}，但 ${result.a}·(${result.b}·${result.c}) = ${result.r}。`,`Associativity fails: (${result.a}·${result.b})·${result.c} = ${result.l}, but ${result.a}·(${result.b}·${result.c}) = ${result.r}.`);
      if(result.kind==='complete'){const first=!completed.has(N);completed.add(N);if(first)options.onComplete?.(N,[...values]);return t(`完成第 ${N-1} 关！每行每列均无重复，${N**3} 个三元组全部满足结合律。你补出了由这些线索唯一确定的 ${level(N).name} 乘法表。`,`Level ${N-1} complete! Every row and column has distinct entries; all ${N**3} triples satisfy associativity. These clues uniquely determine the ${level(N).name} table.`);}
      return t(`已填 ${result.filled}/${N*N} 格；当前可计算的 ${result.checked} 个结合律等式全部成立，尚不能据此判定未填部分。`,`${result.filled}/${N*N} cells filled; all ${result.checked} currently evaluable associativity equations hold. Unfilled cells remain undetermined by this check.`);
    }
    function proofMarkup(){
      const g=level(N),names=g.gens.join(', ');
      const construction=g.kind==='dihedral'?t(`底层元素为 (i,ε)，i∈ℤ/${N/2}ℤ，ε∈ℤ/2ℤ，乘法为 (i,ε)(j,δ)=(i+(−1)^εj,ε+δ)。两种括号展开均为 (i+(−1)^εj+(−1)^(ε+δ)k,ε+δ+η)，故结合律成立。单位元为 (0,0)，逆元为 ((−1)^(ε+1)i,ε)。本关重新编号后得到 ${g.name}，没有改变乘法结构。`,`Underlying elements are (i,ε) in ℤ/${N/2}ℤ × ℤ/2ℤ, with (i,ε)(j,δ)=(i+(−1)^εj,ε+δ). Both bracketings give (i+(−1)^εj+(−1)^(ε+δ)k,ε+δ+η), proving associativity. The identity is (0,0), and the inverse is ((−1)^(ε+1)i,ε). Relabeling yields ${g.name} without changing multiplication.`):
        g.kind==='klein'||g.kind==='plane'?t(`本关把 ${g.name} 的元素重新编号。运算是两个坐标分别作模 ${N===4?2:3} 加法；结合律来自整数加法，零向量是单位元，每个向量的负向量是逆元。`,`This level relabels ${g.name}, with coordinatewise addition modulo ${N===4?2:3}. Associativity follows from integer addition; the zero vector is the identity and the negative vector is the inverse.`):
        t(`本关把 ℤ/${N}ℤ 的元素重新编号。运算来自模 ${N} 加法，故满足结合律；0 被编号为 ${N}，是单位元，每个元素都有加法逆元。`,`This level relabels addition on ℤ/${N}ℤ. It is associative, 0 is labeled ${N} and is the identity, and every element has an additive inverse.`);
      const witness=(N===6||N===8)?(()=>{const [a,b]=g.gens;return `<p>${t(`非交换见证：${a}·${b}=${g.multiply(a,b)}，而 ${b}·${a}=${g.multiply(b,a)}。`,`Noncommutativity: ${a}·${b}=${g.multiply(a,b)}, whereas ${b}·${a}=${g.multiply(b,a)}.`)}</p>`;})():'';
      const certificate=puzzle(N).certificate.map(h=>{
        const r=Math.floor(h.target/N)+1,c=h.target%N+1;
        const reason=h.latin?t(`第 ${h.line+1} ${h.axis?'列':'行'}只缺 ${h.value}`,`${h.axis?'column':'row'} ${h.line+1} is missing only ${h.value}`):`(${h.a}·${h.b})·${h.c} = ${h.a}·(${h.b}·${h.c}), ${h.ab}·${h.c} = ${h.a}·${h.bc}`;
        return `<li><b>m(${r},${c}) = ${h.value}</b> — ${reason}.</li>`;
      }).join('');
      return `<p>${construction}</p>${witness}<p>${t('唯一性证明：下面每一步只使用原始线索或先前已确定的格子。若一行或一列只缺一个元素，该值被行列条件强制确定；若结合律等式一侧的乘积已知，另一侧对应的空格被强制确定。任何满足全部条件的补全都必须逐步同意这些值。证书填满整张表，故至多有一个解；上面的具体群构造提供一个解，故解恰有一个。','Uniqueness proof: each step below uses only clues or previously determined cells. A sole missing element is forced by a row or column; a known side of an associativity equation forces the blank on the other side. Every valid completion must agree with every step. The certificate fills the table, proving at most one solution. The explicit group construction above supplies a solution, proving existence and uniqueness.')}</p><details class="sudoku-certificate"><summary>${t(`逐格证明证书 · ${puzzle(N).certificate.length} 步`,`Cell-by-cell certificate · ${puzzle(N).certificate.length} steps`)}</summary><ol>${certificate}</ol></details><p>${t('这是拉丁方数独，没有宫格规则。素数阶群以及 4 阶、9 阶群都交换；本组关卡中只有 6 阶、8 阶可采用非交换群。','This is a Latin-square puzzle without subgrid rules. Groups of prime order, order 4 and order 9 are abelian; only the order-6 and order-8 levels here can use nonabelian groups.')}</p>`;
    }
    function draw(focusCell=false){
      if(!root.isConnected){dispose();return;}
      const r=Math.floor(selected/N),c=selected%N,filled=values.filter(Boolean).length;
      const cards=options.actionSkills?[["identity",t('单位','Identity'),t('填满单位元所在行和列','Fill the identity row and column')],["inverse",t('逆','Inverse'),t('已知左逆，补出对称位置的右逆','Mirror known left inverses to right inverses')]]:[['identity',t('单位元','Identity'),t(`将单位元 ${N} 标红`,`Mark identity ${N} in red`)],['inverse',t('逆元','Inverses'),t(`寻找乘积为 ${N} 的格子`,`Find products equal to ${N}`)],['cancellation',t('消去律','Cancellation'),t('检查当前行与列','Inspect the selected row/column')],['associativity',t('结合律','Associativity'),t('沿两条路径推出新格','Follow two paths to a new entry')]];
      const cardNote=skill==='identity'?t(`本关单位元是 ${N}。只将数字 ${N} 标红，网格背景保持不变。其单位元性质由本关的唯一补全证明确定。`,`The identity is ${N}. Only the digit ${N} turns red; cell backgrounds stay unchanged. Its identity property follows from the unique-completion proof for this level.`):
        skill==='inverse'?t(`标出已填且乘积为单位元 ${N} 的数字；完整表中，第 x 行的这一个列标就是 x 的逆元。`,`Marked entries have product equal to the identity ${N}. In the completed table, that column label in row x is the inverse of x.`):
        skill==='cancellation'?t('所选格子的行和列已标出。每行无重复对应左消去律，每列无重复对应右消去律。','The selected row and column are highlighted. Distinct row entries encode left cancellation; distinct column entries encode right cancellation.'):
        skill==='associativity'?t('用 (a·b)·c = a·(b·c) 连接四个格子。先算括号，不可交换因子。','Connect four cells using (a·b)·c = a·(b·c). Evaluate the parentheses first; do not swap factors.'):t('选择技能卡，查看它在乘法表中的含义。','Choose a skill card to see its meaning in the table.');
      root.innerHTML=`<nav class="sudoku-levels" ${options.fixedLevel?'hidden':''} aria-label="${t('选择关卡','Choose level')}">${Array.from({length:8},(_,i)=>i+2).map(n=>`<button type="button" data-level="${n}" aria-pressed="${N===n}">${n}×${n}${completed.has(n)?' ✓':''}</button>`).join('')}</nav><div class="sudoku-intro"><p>${N} × ${N} · ${t('拉丁方数独','Latin-square puzzle')}</p><span>${filled}/${N*N}</span></div><p class="sudoku-rules">${t(`填入 1—${N}，每行每列各出现一次，并满足结合律。没有宫格规则。${N===2?'本关先用行列无重复补出最后一格。':'线索和空缺分散在表中，结合行列条件与结合律逐格推导。'}`,`Enter 1–${N} once in each row and column, with associativity. No subgrid rule. ${N===2?'Start by completing the last cell using no repetitions.':'Clues and blanks are scattered; combine row/column rules with associativity.'}`)}</p>
      <div class="sudoku-cards">${cards.map(([id,title,desc])=>`<button type="button" data-skill="${id}" title="${skillLocked(id)?unlockNote(id):desc}" data-unlock-label="${id==='identity'?'3×3':'5×5'}" ${skillLocked(id)?'disabled':''} aria-pressed="${skill===id}"><strong>${title}</strong><span>${skillLocked(id)?unlockNote(id):desc}</span></button>`).join('')}</div><p class="sudoku-card-note">${cardNote}</p>
      <div class="sudoku-play"><div class="sudoku-table-wrap"><table class="sudoku-table" style="--sudoku-size:${N}"><caption>${t('行元素 × 列元素；浅色数字为给定线索','Row factor × column factor; muted numbers are given clues')}</caption><thead><tr><th scope="col">·</th>${Array.from({length:N},(_,i)=>`<th scope="col" class="${skill==='identity'&&i===N-1?'identity-mark':''}">${i+1}</th>`).join('')}</tr></thead><tbody>${Array.from({length:N},(_,row)=>`<tr><th scope="row" class="${skill==='identity'&&row===N-1?'identity-mark':''}">${row+1}</th>${Array.from({length:N},(_,col)=>{
        const i=index(row,col),v=values[i],classes=[given(i)?'given':'',i===selected?'selected':'',skill==='identity'&&v===N?'identity-mark':'',skill==='inverse'&&v===N?'inverse-mark':'',skill==='cancellation'&&(row===r||col===c)?'cancel-mark':'',skill==='associativity'&&hint?.cells.includes(i)?'path-mark':'',hint?.target===i?'target-mark':'',issue?.cells?.includes(i)?'error-mark':''].filter(Boolean).join(' ');
        return `<td><button type="button" data-cell="${i}" class="${classes}" tabindex="${i===selected?0:-1}" aria-label="${t(`第 ${row+1} 行，第 ${col+1} 列；${v||'空白'}${given(i)?'，已知':''}`,`Row ${row+1}, column ${col+1}; ${v||'blank'}${given(i)?', given':''}`)}" aria-pressed="${i===selected}">${v||'<span aria-hidden="true">·</span>'}</button></td>`;
      }).join('')}</tr>`).join('')}</tbody></table></div><div class="sudoku-tools"><p>${t('当前格','Selected cell')}：${r+1} · ${c+1}</p><div class="sudoku-digits">${Array.from({length:N},(_,i)=>`<button type="button" data-digit="${i+1}" ${given(selected)?'disabled':''}>${i+1}</button>`).join('')}</div><button type="button" data-action="erase" ${given(selected)?'disabled':''}>${t('清除此格','Clear cell')}</button><button type="button" data-action="check">${t('检查行列与结合律','Check rows, columns & associativity')}</button><button type="button" data-action="reset">${t('重新开始','Restart')}</button></div></div>
      <div class="sudoku-deduction" ${hint?'':'hidden'}>${hint?`<p>${hint.latin?t(`第 ${hint.line+1} ${hint.axis?'列':'行'}缺哪个元素？`,`Which element is missing in ${hint.axis?'column':'row'} ${hint.line+1}?`):t('同一乘积，两条路径','One product, two paths')}</p><div class="sudoku-paths" ${hint.latin?'hidden':''}><p>(${hint.a} · ${hint.b}) · ${hint.c} = ${hint.ab} · ${hint.c} = ${hint.target===hint.left?'?':hint.value}</p><p>${hint.a} · (${hint.b} · ${hint.c}) = ${hint.a} · ${hint.bc} = ${hint.target===hint.right?'?':hint.value}</p></div><button type="button" data-action="apply">${hint.latin?t(`由行列无重复填入 ${hint.value}`,`Use no repetitions to enter ${hint.value}`):t(`由结合律填入 ${hint.value}`,`Use associativity to enter ${hint.value}`)}</button>`:''}</div>
      ${!options.fixedLevel&&completed.has(N)&&N<9?`<button type="button" data-level="${N+1}">${t(`进入 ${N+1}×${N+1} 下一关 →`,`Next level: ${N+1}×${N+1} →`)}</button>`:''}<p class="sudoku-status" role="status">${message||(options.fixedLevel?t('数字键填数 · 方向键移动 · 退格删除 · 进度自动保存于本机。','Number keys to enter · Arrows to move · Backspace to erase · Progress saved on this device.'):t('可用数字键填数、方向键移动、退格删除。空格和回车在游戏内不会跳到下一讲。','Use number keys, arrow keys and Backspace. Space and Enter within the game do not advance the lesson.'))}</p>
      <details class="sudoku-proof" ${proofOpen?'open':''}><summary>${t('为什么这些线索能唯一确定整张表？','Why do these clues determine a unique table?')}</summary>${proofMarkup()}</details>`;
      root.querySelector('details').addEventListener('toggle',e=>{proofOpen=e.currentTarget.open;});
      if(focusCell&&!options.sceneBoard)root.querySelector(`[data-cell="${selected}"]`)?.focus({preventScroll:true});
      options.onRender?.({n:N,values:[...values],selected,skill,hint,issue,cells:[...root.querySelectorAll('[data-cell]')].map(b=>({classes:b.className,label:b.getAttribute('aria-label')}))});
    }
    function enter(value){if(given(selected))return;values[selected]=value;changed();hint=null;issue=null;message='';if(values.every(Boolean)){issue=inspect(values);message=feedback(issue);}draw(true);}
    function useHint(){
      issue=inspect(values);if(issue.kind==='repeat'||issue.kind==='associativity'){message=feedback(issue);hint=null;return;}
      issue=null;hint=deduction(values,selected);if(hint){selected=hint.target;message='';}else message=feedback(inspect(values));
    }
    root.addEventListener('click',event=>{
      const button=event.target.closest('button');if(!button)return;
      if(button.dataset.level){N=+button.dataset.level;values=initial(N);selected=initial(N).findIndex(v=>!v);skill='';hint=null;issue=null;message='';proofOpen=false;draw();return;}
      if(button.dataset.cell!==undefined){selected=+button.dataset.cell;draw(true);return;}
      if(button.dataset.digit){enter(+button.dataset.digit);return;}
      if(button.dataset.skill){if(skillLocked(button.dataset.skill))return;if(options.actionSkills){skill=button.dataset.skill;const result=applySkill(values,skill);hint=null;issue=null;if(result.conflicts.length){issue={cells:result.conflicts};message=t('对称位置已有冲突，请先检查这些数字。','A transposed cell conflicts. Check those entries first.');}else{values=result.values;changed();message=skill==='identity'?t(`单位元为 ${N}：已填满其所在行和列。`,`Identity ${N}: its row and column are complete.`):t(`由 ba=e ⇒ ab=e，补入 ${result.changed.length} 个对称位置。`,`From ba=e ⇒ ab=e, filled ${result.changed.length} transposed cells.`);if(values.every(Boolean)){issue=inspect(values);message=feedback(issue);}}draw();return;}skill=skill===button.dataset.skill?'':button.dataset.skill;hint=null;issue=null;message='';if(skill==='associativity')useHint();draw();return;}
      switch(button.dataset.action){
        case 'erase':enter(0);return;
        case 'check':issue=inspect(values);message=feedback(issue);break;
        case 'reset':values=initial(N);changed();selected=initial(N).findIndex(v=>!v);hint=null;issue=null;message='';skill='';break;
        case 'apply':if(hint){values[hint.target]=hint.value;changed();hint=null;issue=null;message=feedback(inspect(values));useHint();}break;
      }
      draw();
    },{signal:abort.signal});
    root.addEventListener('keydown',event=>{
      if(event.key===' '||event.key==='Enter'){event.stopPropagation();return;}
      if(!event.target.closest('[data-cell]'))return;
      const offsets={ArrowLeft:-1,ArrowRight:1,ArrowUp:-N,ArrowDown:N};
      if(event.key in offsets){event.preventDefault();event.stopPropagation();selected=(selected+offsets[event.key]+N*N)%(N*N);draw(true);}
      else if(/^[1-9]$/.test(event.key)&&+event.key<=N){event.preventDefault();event.stopPropagation();enter(+event.key);}
      else if(['Backspace','Delete'].includes(event.key)){event.preventDefault();event.stopPropagation();enter(0);}
    },{signal:abort.signal});
    window.addEventListener('course-language',()=>{message='';draw();},{signal:abort.signal});draw();return {select:i=>{if(i>=0&&i<N*N){selected=i;draw();}},enter:value=>enter(value),destroy:()=>{abort.abort();root.remove();}};
  }};
})();
