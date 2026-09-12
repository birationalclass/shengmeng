import {proofPanel} from './proof-panel.js?v=99';
// Page cohomology belongs to the mathematical exposition, below the page diagram.
// These kernels and images are subspaces on E_r; they are not the filtered-total
// spaces Z_r and B_r introduced later in the notebook.
function cohomologyDetail({r,phase,point,math,t}) {
 const {p,q}=point,ip=p-r,iq=q+r-1,op=p+r,oq=q-r+1;
 const incomingZero=ip<0||iq<0,outgoingZero=op<0||oq<0;
 const E=(a,b)=>a<0||b<0?'0':`E_{${r}}^{${a},${b}}`,map=`d_{${r}}^{${p},${q}}`,input=`d_{${r}}^{${ip},${iq}}`;
 const shift=(x,n)=>n===0?x:`${x}${n>0?'+':''}${n}`;
 const names=[t('复形','Complex'),t('取核','Kernel'),t('像包含于核','Image in kernel'),t('取商','Quotient')];
 const formulas=[
  [`${E(ip,iq)}\\xrightarrow{d_{${r}}}${E(p,q)}\\xrightarrow{d_{${r}}}${E(op,oq)}`,`d_{${r}}^2=0`],
  [`\\ker ${map}=\\{z\\in ${E(p,q)}:${map}z=0\\}`],
  [`\\operatorname{im}(${input})\\subseteq\\ker(${map})`,`d_{${r}}(d_{${r}}y)=0`],
  [r===0?'E_1^{p,q}\\cong H^q(E_0^{p,\\bullet},d_0)\\cong H^q(K^{p,\\bullet},\\delta_2)':`E_{${r+1}}^{p,q}\\cong\\frac{\\ker(d_{${r}}:E_{${r}}^{p,q}\\to E_{${r}}^{${shift('p',r)},${shift('q',1-r)}})}{\\operatorname{im}(d_{${r}}:E_{${r}}^{${shift('p',-r)},${shift('q',r-1)}}\\to E_{${r}}^{p,q})}`,
   `E_{${r+1}}^{${p},${q}}\\cong\\frac{\\ker(${map})}{\\operatorname{im}(${input})}`]
 ][phase];
 let diagram='';
 if(phase===1||phase===2){
  diagram=`<div class="co-subspace-diagram"><span class="co-ambient-name">${math(E(p,q))}</span><div class="co-kernel-region"><span>${math(outgoingZero?`\\ker(${map})=${E(p,q)}`:`\\ker(${map})`)}</span>${phase===2?`<span class="co-image-region">${math(incomingZero?`\\operatorname{im}(${input})=0`:`\\operatorname{im}(${input})`)}</span>`:''}</div></div>`;
 }
 if(phase===3){
  const reps=incomingZero?math('z'):math('z,\\ z+b');
  diagram=`<div class="co-quotient-diagram"><div class="co-domain"><span>${math(`\\ker(${map})`)}</span><span class="co-representatives">${reps}</span></div><span class="co-projection">${math('\\xrightarrow{\\Psi^{-1}\\pi}')}</span><div class="co-codomain"><span>${math(`E_{${r+1}}^{${p},${q}}`)}</span><span class="co-class-symbol">${math('\\Psi^{-1}([z]_H)')}</span></div></div>`;
  formulas.push(incomingZero?'\\pi(z+0)=\\pi(z)=[z]_H':`\\pi(z+b)=\\pi(z)=[z]_H,\\qquad b\\in\\operatorname{im}(${input})`);
 }
 const notes=[r===0?t('固定一列，对每个位置取上同调，组成右上方的下一页。','Take cohomology in each column to form the next page above.'):t('微分的双次数为 (r,1−r)。','The differential has bidegree (r,1−r).'),t('区域只表示子空间的包含关系，不表示维数。','Regions indicate subspace inclusion, not dimension.'),t('因为微分的平方为零，所有边界都是闭元。','Every boundary is a cocycle because the differential squares to zero.'),t('此商是上同调空间，与下一页自然同构。π 映到该上同调空间，Ψ⁻¹ 将上同调类送到下一页；新微分由 D 诱导。','This cohomology quotient is naturally isomorphic to the next page. The map π takes a cocycle to its cohomology class; Ψ⁻¹ then identifies it with the next page. The new differential is induced by D.')];
 return `<div class="operation-content evolution-exposition">${formulas.slice(0,phase===3?2:formulas.length).map(f=>`<div class="operation-equation">${math(f,true)}</div>`).join('')}${diagram}${phase===3?`<div class="operation-equation">${math(formulas[2],true)}</div>`:''}</div><p class="operation-note">${notes[phase]}</p>`;
}

export function cohomologyExposition({r,point,math,t,language}){
 const names=[t('复形','Complex'),t('核','Kernel'),t('像包含于核','Image lies in the kernel'),t('上同调商','Cohomology quotient')];
 const details=names.map((name,phase)=>`<section class="proof-detail-section"><h3>${name}</h3>${cohomologyDetail({r,phase,point,math,t})}</section>`).join('');
 return proofPanel({key:'page-cohomology',title:t('从本页到下一页','From one page to the next'),formulas:[String.raw`E_{r+1}^{p,q}\cong\frac{\ker d_r^{p,q}}{\operatorname{im}d_r^{p-r,q+r-1}}`],note:t(`此处 ${math('r='+r)}。由 ${math('d_r^2=0')}，像包含于核；取商得到上同调，与下一页自然同构。`,`Here ${math('r='+r)}. Since ${math('d_r^2=0')}, the image lies in the kernel; the quotient is cohomology, naturally isomorphic to the next page.`),details,math,language});
}
