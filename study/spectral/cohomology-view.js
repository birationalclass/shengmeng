// Page cohomology belongs to the mathematical exposition, below the page diagram.
// These kernels and images are subspaces on E_r; they are not the filtered-total
// spaces Z_r and B_r introduced later in the notebook.
export function cohomologyExposition({r,phase,point,math,t}) {
 const {p,q}=point,ip=p-r,iq=q+r-1,op=p+r,oq=q-r+1;
 const incomingZero=ip<0||iq<0,outgoingZero=op<0||oq<0;
 const E=(a,b)=>a<0||b<0?'0':`E_{${r}}^{${a},${b}}`,map=`d_{${r}}^{${p},${q}}`,input=`d_{${r}}^{${ip},${iq}}`;
 const shift=(x,n)=>n===0?x:`${x}${n>0?'+':''}${n}`;
 const names=[t('复形','Complex'),t('取核','Kernel'),t('像包含于核','Image in kernel'),t('取商','Quotient')];
 const tabs=`<nav class="co-exposition-tabs" aria-label="${t('上同调构造的原理','How page cohomology is formed')}">${names.map((name,i)=>`<button data-co-phase="${i}" aria-pressed="${phase===i}">${name}</button>`).join('')}</nav>`;
 const formulas=[
  [`${E(ip,iq)}\\xrightarrow{d_{${r}}}${E(p,q)}\\xrightarrow{d_{${r}}}${E(op,oq)}`,`d_{${r}}^2=0`],
  [`\\ker ${map}=\\{z\\in ${E(p,q)}:${map}z=0\\}`],
  [`\\operatorname{im}(${input})\\subseteq\\ker(${map})`,`d_{${r}}(d_{${r}}y)=0`],
  [r===0?'E_1^{p,q}=H^q(E_0^{p,\\bullet},d_0)\\cong H^q(K^{p,\\bullet},\\delta_2)':`E_{${r+1}}^{p,q}\\cong\\frac{\\ker(d_{${r}}:E_{${r}}^{p,q}\\to E_{${r}}^{${shift('p',r)},${shift('q',1-r)}})}{\\operatorname{im}(d_{${r}}:E_{${r}}^{${shift('p',-r)},${shift('q',r-1)}}\\to E_{${r}}^{p,q})}`,
   `E_{${r+1}}^{${p},${q}}\\cong\\frac{\\ker(${map})}{\\operatorname{im}(${input})}`]
 ][phase];
 let diagram='';
 if(phase===1||phase===2){
  diagram=`<div class="co-subspace-diagram"><span class="co-ambient-name">${math(E(p,q))}</span><div class="co-kernel-region"><span>${math(outgoingZero?`\\ker(${map})=${E(p,q)}`:`\\ker(${map})`)}</span>${phase===2?`<span class="co-image-region">${math(incomingZero?`\\operatorname{im}(${input})=0`:`\\operatorname{im}(${input})`)}</span>`:''}</div></div>`;
 }
 if(phase===3){
  const reps=incomingZero?math('z'):math('z,\\ z+b');
  diagram=`<div class="co-quotient-diagram"><div class="co-domain"><span>${math(`\\ker(${map})`)}</span><span class="co-representatives">${reps}</span></div><span class="co-projection">${math('\\xrightarrow{\\quad\\pi\\quad}')}</span><div class="co-codomain"><span>${math(`E_{${r+1}}^{${p},${q}}`)}</span><span class="co-class-symbol">${math('[z]')}</span></div></div>`;
  formulas.push(incomingZero?'\\pi(z+0)=\\pi(z)=[z]':`\\pi(z+b)=\\pi(z)=[z],\\qquad b\\in\\operatorname{im}(${input})`);
 }
 const notes=[r===0?t('固定一列，对每个位置取上同调，组成右上方的下一页。','Take cohomology in each column to form the next page above.'):t('微分的双次数为 (r,1−r)。','The differential has bidegree (r,1−r).'),t('区域只表示子空间的包含关系，不表示维数。','Regions indicate subspace inclusion, not dimension.'),t('因为微分的平方为零，所有边界都是闭元。','Every boundary is a cocycle because the differential squares to zero.'),t('在每个 (p,q) 取这个商，组成新页。π 的定义域是核；新页的微分由 D 诱导。','This quotient at each (p,q) forms the new page. The domain of π is the kernel; the new differential is induced by D.')];
 return `${tabs}<div class="operation-content evolution-exposition">${formulas.slice(0,phase===3?2:formulas.length).map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}${diagram}${phase===3?`<div class="operation-equation">${math(formulas[2],true)}</div>`:''}</div><p class="operation-note">${notes[phase]}</p>`;
}
