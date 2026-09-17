import {proofPanel} from './proof-panel.js?v=150';
const R=String.raw;
export function filteredSubcomplexExposition({concept,math,language}){
 const t=(z,e)=>language()==='en'?e:z,M=f=>math(f),eq=f=>`<div class="operation-equation">${math(f,true)}</div>`;
 if(concept==='subcomplex')return `<p class="operation-note">${t(`由 1.9，这是 ${M(R`(C^\ast,D)`)} 的子复形。`,`This is a subcomplex of ${M(R`(C^\ast,D)`)} by 1.9.`)}</p>`;
 const map=R`\begin{array}{rcl}H^n(F^pC^\bullet,D)&\xrightarrow{H^n(\iota_p)}&H^n(C^\bullet,D)\\[.5em]a+D(F^pC^{n-1})&\longmapsto&a+D(C^{n-1})\end{array}`;
 const details=`<p>${t(`包含 ${M(R`\iota_p`)} 与微分交换，因此它是复形间的映射，由上同调的函子性诱导所述映射。`,`The inclusion ${M(R`\iota_p`)} commutes with the differential, so it is a cochain map and induces the stated map by functoriality of cohomology.`)}</p>`+
 eq(R`D\circ\iota_p^n=\iota_p^{n+1}\circ D|_{F^pC^n}`)+
 `<p>${t(`具体地，取闭元 ${M(R`a\in F^pC^n`)}，包含映射仍将其送到闭元 ${M('a')}。若换取同一上同调类的代表元，则`,`Explicitly, a cocycle ${M(R`a\in F^pC^n`)} is sent to the same cocycle ${M('a')}. Changing its representative in the source gives`)}</p>`+
 eq(R`a'-a=Db,\quad b\in F^pC^{n-1}\subseteq C^{n-1}\quad\Longrightarrow\quad a'+D(C^{n-1})=a+D(C^{n-1})`)+
 `<p>${t('故映射良定义，并由代表元上的线性运算得到线性映射。','Thus the map is well-defined, and linearity follows from the linear operations on representatives.')}</p>`;
 return proofPanel({key:'filtered-inclusion',title:t('1.11 包含所诱导的上同调映射','1.11 The inclusion-induced map on cohomology'),formulas:[map],note:t(`其中 ${M(R`a\in F^pC^n`)} 且 ${M('Da=0')}；${M(R`\iota_p`)} 是复形间的映射，因而诱导上同调映射。`,`Here ${M(R`a\in F^pC^n`)} and ${M('Da=0')}; the cochain map ${M(R`\iota_p`)} induces the map on cohomology.`),details,math,language});
}
