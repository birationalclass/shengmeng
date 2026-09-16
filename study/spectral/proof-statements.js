import {kmVanishingProof} from './km-vanishing.js?v=140';
import {singleLineContent} from './single-line-convergence.js?v=140';
// Full hypotheses and conclusions live with the shared proof presentation.
// The compact formula shown in the notebook is not a theorem statement.
export function proofStatement({key,formulas,math,english}){
 const R=String.raw,t=(z,e)=>english?e:z,M=x=>math(x),eq=x=>`<div class="operation-equation">${math(x,true)}</div>`;
 let assumptions='',hypothesisFormulas=[],conclusions=formulas,conclusionBody='',conclusionLead=t('则有：','Then the following holds:'),kind=t('命题。','Proposition.');
 const filtered=t(`设 ${M(R`(C^\bullet,D)`)} 是带递减子复形滤过 ${M(R`F^\bullet C^\bullet`)} 的上链复形；${M(R`(E_r^{p,q},d_r^{p,q})`)} 是由该滤过构造的上同调型谱序列，微分双次数为 ${M('(r,1-r)')}。`,`Let ${M(R`(C^\bullet,D)`)} be a cochain complex with a decreasing filtration ${M(R`F^\bullet C^\bullet`)} by subcomplexes. Let ${M(R`(E_r^{p,q},d_r^{p,q})`)} be its cohomological spectral sequence, with differential of bidegree ${M('(r,1-r)')}.`);
 const first=t('另假设滤过来自第一象限双复形的列滤过。','Assume further that this is the column filtration of a first-quadrant double complex.');
 if(key.startsWith('leray-')){
  const page=Number(key.slice(6));
  const setup=t(`设 ${M('f:X\\to Y')} 是域上概形的态射，${M(R`\mathcal F`)} 是 ${M('X')} 上的拟凝聚层。取其在所有 ${M(R`\mathcal O_X`)}-模层中的内射分解 ${M(R`\mathcal{I}^\bullet`)}，令 ${M(R`\mathcal{A}^\bullet=f_*\mathcal{I}^\bullet`)}。`,`Let ${M('f:X\\to Y')} be a morphism of schemes over a field and ${M(R`\mathcal F`)} a quasi-coherent sheaf on ${M('X')}. Choose an injective resolution ${M(R`\mathcal{I}^\bullet`)} in all ${M(R`\mathcal O_X`)}-module sheaves, and put ${M(R`\mathcal{A}^\bullet=f_*\mathcal{I}^\bullet`)}.`);
  assumptions=setup;
  if(page<=4){kind=t('设定与陈述。','Setup and statement.');conclusionLead='';}
  if(page===5||page===6){
   assumptions+=t(`记 ${M(R`\mathcal B^q=\operatorname{im}d_{\mathcal A}^{q-1}`)}、${M(R`\mathcal Z^q=\ker d_{\mathcal A}^q`)}、${M(R`\mathcal H^q=\mathcal Z^q/\mathcal B^q`)}。给定内射分解 ${M(R`\mathcal B^q\to\mathcal U^{\bullet,q}`)} 和 ${M(R`\mathcal H^q\to\mathcal V^{\bullet,q}`)}。`,`Write ${M(R`\mathcal B^q=\operatorname{im}d_{\mathcal A}^{q-1}`)}, ${M(R`\mathcal Z^q=\ker d_{\mathcal A}^q`)}, and ${M(R`\mathcal H^q=\mathcal Z^q/\mathcal B^q`)}. Fix injective resolutions ${M(R`\mathcal B^q\to\mathcal U^{\bullet,q}`)} and ${M(R`\mathcal H^q\to\mathcal V^{\bullet,q}`)}.`);
   conclusionLead=t(`则存在相容内射分解 ${M(R`\mathcal Z^q\to\mathcal W^{\bullet,q}`)} 和 ${M(R`\mathcal A^q\to\mathcal J^{\bullet,q}`)}，使下列复形短正合列与原层短正合列相容且逐项分裂：`,`Then there exist compatible injective resolutions ${M(R`\mathcal Z^q\to\mathcal W^{\bullet,q}`)} and ${M(R`\mathcal A^q\to\mathcal J^{\bullet,q}`)} fitting into the following degreewise split exact sequences, which lift the original sheaf sequences:`);
   conclusions=[R`0\to\mathcal U^{\bullet,q}\to\mathcal W^{\bullet,q}\to\mathcal V^{\bullet,q}\to0`,R`0\to\mathcal W^{\bullet,q}\to\mathcal J^{\bullet,q}\to\mathcal U^{\bullet,q+1}\to0`];
   if(page===6){
    conclusionLead=t(`则可取下列直和模型及相容微分 ${M('h,v')}，使 ${M(R`(\mathcal J,h,v)`)} 成为 ${M(R`\mathcal A^\bullet`)} 的 Cartan–Eilenberg 内射分解，且满足：`,`Then the following direct-sum model admits compatible differentials ${M('h,v')} making ${M(R`(\mathcal J,h,v)`)} a Cartan–Eilenberg injective resolution of ${M(R`\mathcal A^\bullet`)}, with the following identities:`);
    conclusions=[R`\mathcal W^{p,q}=\mathcal U^{p,q}\oplus\mathcal V^{p,q},\quad\mathcal J^{p,q}=\mathcal W^{p,q}\oplus\mathcal U^{p,q+1}`,R`\ker v^{p,q}=\mathcal W^{p,q},\quad\operatorname{im}v^{p,q-1}=\mathcal U^{p,q},\quad\mathcal H_v^q(\mathcal J^{p,\bullet})\cong\mathcal V^{p,q}`];
   }
  }
  if(page>=7&&page<=12){
   assumptions+=t(`取 ${M(R`\mathcal{A}^\bullet`)} 的 Cartan–Eilenberg 内射分解 ${M('(\\mathcal{J},h,v)')}，采用 ${M('hv=vh')} 的约定。令 ${M(R`K^{p,q}=\Gamma(Y,\mathcal{J}^{p,q})`)}、${M(R`\delta_1=\Gamma(h)`)}、${M(R`\delta_2|_{K^{p,q}}=(-1)^p\Gamma(v)`)}，并令 ${M(R`C^\bullet=\operatorname{Tot}K`)}、${M(R`D=\delta_1+\delta_2`)}；谱序列取列滤过。`,`Choose a Cartan–Eilenberg injective resolution ${M('(\\mathcal{J},h,v)')} of ${M(R`\mathcal{A}^\bullet`)}, with ${M('hv=vh')}. Put ${M(R`K^{p,q}=\Gamma(Y,\mathcal{J}^{p,q})`)}, ${M(R`\delta_1=\Gamma(h)`)}, ${M(R`\delta_2|_{K^{p,q}}=(-1)^p\Gamma(v)`)}, ${M(R`C^\bullet=\operatorname{Tot}K`)}, and ${M(R`D=\delta_1+\delta_2`)}. Use the column filtration.`);
   if(page===8)conclusions=[R`\delta_1^2=\delta_2^2=\delta_1\delta_2+\delta_2\delta_1=0`];
   if(page===10)conclusions=[R`E_2^{p,q}\cong H^p(Y,R^qf_*\mathcal F)`];
   if(page===11)conclusions=[R`H^n(C^\bullet,D)\cong H^n(X,\mathcal F)`];
   if(page===12)conclusions=[R`E_2^{p,q}\cong H^p(Y,R^qf_*\mathcal F)\Longrightarrow H^{p+q}(X,\mathcal F)`];
  }
  if(page===13){
   const single=singleLineContent({math,t});
   assumptions=single.assumptions;
   hypothesisFormulas=single.filtration;
   conclusionLead=t(`则对每个 ${M(R`n\ge0`)}，分别有以下结论。`,`Then, for every ${M(R`n\ge0`)}, the following two assertions hold.`);
   conclusionBody=`<p>${t(`若对所有 ${M(R`p>0,q\ge0`)} 都有 ${M(R`E_{r_0}^{p,q}=0`)}（仅第零列可能非零），则边缘映射为同构：`,`If ${M(R`E_{r_0}^{p,q}=0`)} for all ${M(R`p>0,q\ge0`)} (only column zero may be nonzero), then the edge map is an isomorphism:`)}</p>${eq(R`H^n\xrightarrow{\sim}E_{r_0}^{0,n}`)}<p>${t(`若对所有 ${M(R`q>0,p\ge0`)} 都有 ${M(R`E_{r_0}^{p,q}=0`)}（仅第零行可能非零），则边缘映射为同构：`,`If ${M(R`E_{r_0}^{p,q}=0`)} for all ${M(R`q>0,p\ge0`)} (only row zero may be nonzero), then the edge map is an isomorphism:`)}</p>${eq(R`E_{r_0}^{n,0}\xrightarrow{\sim}H^n`)}`;
  }
  if(page===14){
   ({assumptions,hypothesisFormulas,conclusionLead,conclusions}=kmVanishingProof({math,t}));
  }
  if(page===15){conclusionLead=t(`则对每个 ${M('n\\ge0')}，自然映射为同构：`,`Then, for every ${M('n\\ge0')}, the natural map is an isomorphism:`);assumptions=t(`设 ${M('X')} 是正规复代数簇，${M(R`\pi:\widetilde X\to X`)} 是解消，满足 ${M(R`\pi_*\mathcal O_{\widetilde X}=\mathcal O_X`)} 及 ${M(R`R^q\pi_*\mathcal O_{\widetilde X}=0`)}（${M('q>0')}）。`,`Let ${M('X')} be a normal complex variety and ${M(R`\pi:\widetilde X\to X`)} a resolution satisfying ${M(R`\pi_*\mathcal O_{\widetilde X}=\mathcal O_X`)} and ${M(R`R^q\pi_*\mathcal O_{\widetilde X}=0`)} for ${M('q>0')}.`);conclusions=[R`H^n(X,\mathcal O_X)\xrightarrow{\sim}H^n(\widetilde X,\mathcal O_{\widetilde X})`];}
 }else{
  assumptions=filtered;
  if(['er','e1','d0','d1','dr','filtered-Z','filtered-B'].includes(key)){kind=t('设定与陈述。','Setup and statement.');conclusionLead='';}
  if(['stable-term','stabilization'].includes(key)){
   assumptions+=first+t(`固定 ${M(R`p,q\ge0`)}。`,`Fix ${M(R`p,q\ge0`)}.`);
   conclusionLead=t(`则对所有 ${M(R`s\ge\max\{p+1,q+2\}`)}，该位置的入射、出射微分均为零，且下列映射为自然同构：`,`Then, for every ${M(R`s\ge\max\{p+1,q+2\}`)}, both incoming and outgoing differentials at this position vanish, and the following map is a natural isomorphism:`);
   conclusions=[R`E_s^{p,q}\xrightarrow{\sim}E_{s+1}^{p,q},\quad[a]_s\longmapsto[a]_{s+1}`];
  }
  if(key==='page-cohomology'){
   conclusionLead=t(`则对每个 ${M(R`r\ge0`)} 及每个双次数 ${M('(p,q)')}，有自然同构：`,`Then, for every ${M(R`r\ge0`)} and bidegree ${M('(p,q)')}, there is a natural isomorphism:`);
   conclusions=[R`\Psi_{r+1}^{p,q}:E_{r+1}^{p,q}\xrightarrow{\sim}\frac{\ker d_r^{p,q}}{\operatorname{im}d_r^{p-r,q+r-1}},\quad[a]_{r+1}\longmapsto[a]_r+\operatorname{im}d_r^{p-r,q+r-1}`];
  }
  if(key==='page-transition'){
   conclusionLead=t('则对每个非负页数和双次数，有自然短正合列：','Then, for each nonnegative page and each bidegree, there is a natural short exact sequence:');
   conclusions=[R`0\to\operatorname{im}d_r^{p-r,q+r-1}\to\ker d_r^{p,q}\xrightarrow{\pi_r^{p,q}}E_{r+1}^{p,q}\to0`];
  }
  if(key.startsWith('abutment-'))assumptions+=first;
  if(key==='abutment-degeneration')assumptions+=t(`并假设该谱序列收敛到带诱导滤过的 ${M(R`H^n=H^n(C^\bullet,D)`)}，且 ${M(R`d_s=0\ (s\ge r_0)`)}。`,`Assume it converges to ${M(R`H^n=H^n(C^\bullet,D)`)} with the induced filtration and ${M(R`d_s=0\ (s\ge r_0)`)}.`);
  if(key==='abutment-convergence')assumptions+=t(`目标滤过定义为 ${M(R`F^pH^n=\operatorname{im}(H^n(F^pC)\to H^n(C))`)}。`,`The target filtration is ${M(R`F^pH^n=\operatorname{im}(H^n(F^pC)\to H^n(C))`)}.`);
 }
 return `<section class="proof-statement"><div class="proof-hypotheses"><p><strong>${kind}</strong> ${assumptions}</p>${hypothesisFormulas.map(eq).join('')}</div>${conclusionLead?`<p class="proof-conclusion-lead">${conclusionLead}</p>`:''}<div class="proof-conclusions">${conclusionBody||conclusions.map(eq).join('')}</div></section>`;
}
