import {Complex,examples,texVector,matrixTex,q,rank,basisVector} from './algebra.js';
import {lessons,convergence,initial,totalCohomology} from './content.js';
import {translatePage,language,toggleLanguage} from './language.js';
const $=s=>document.querySelector(s),raw=String.raw;
const state={module:'initial',cover:true,reveal:0,buildStep:0,pinned:null,step:0,n:3,p:1,r:0,direction:'both',example:'survive',lambda:0,selected:null,playing:false};
let timer=null;const complexes=Object.fromEntries(Object.entries(examples).map(([k,x])=>[k,new Complex(x)]));
const traceComplex=new Complex({...examples.d2,gens:[...examples.d2.gens,{id:'x',p:0,q:0},{id:'y',p:0,q:1}],v:[...examples.d2.v,['x','y',1]]});
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const math=(tex,display=false)=>katex.renderToString(tex,{displayMode:display,throwOnError:true,strict:'error',trust:false});
const block=(t,concept='')=>`<div class="math-block" data-formula="${esc(t)}" ${concept?`data-concept="${concept}"`:''} role="button" tabindex="0" aria-label="${concept?'悬停对照，点击固定高亮':'放大查看公式'}">${math(t,true)}<button class="formula-zoom" data-zoom aria-label="放大查看公式" title="点击放大公式">↗</button></div>`;
const scene=()=>state.module==='trace'?traceComplex:complexes[state.example];
const pageR=()=>state.module==='converge'?scene().maxP+2:state.r;
const stepCount=()=>({initial:initial.length,learn:lessons.length-1,lab:scene().maxP+3,trace:6,converge:convergence.length})[state.module];
let layout={dx:125,dy:79};
const xy=(p,q)=>[105+p*layout.dx,435-q*layout.dy];
const shifted=(s,k)=>k===0?s:`${s}${k>0?'+':''}${k}`;
function label(x,y,tex,w=116,h=38,small=false){return `<foreignObject x="${x-w/2}" y="${y-h/2}" width="${w}" height="${h}"><div xmlns="http://www.w3.org/1999/xhtml" class="math-label ${small?'small-label':''}">${math(tex)}</div></foreignObject>`;}
function line(x1,y1,x2,y2,type,hot,tex=''){let dx=x2-x1,dy=y2-y1,len=Math.hypot(dx,dy),pad=Math.min(dx===0?Infinity:52*len/Math.abs(dx),dy===0?Infinity:21*len/Math.abs(dy))+5;const f=pad/len;x1+=dx*f;y1+=dy*f;x2-=dx*f;y2-=dy*f;let out=`<path data-concept="${arrowConcept(type)}" tabindex="0" role="button" aria-label="${arrowConcept(type)}" class="arrow ${type} ${hot?'hot':''} ${state.playing?'animating':''}" d="M${x1},${y1} L${x2},${y2}" marker-end="url(#arrow-${type})"/>`;if(tex)out+=label((x1+x2)/2+(dx===0?26:0),(y1+y2)/2+(dy===0?-17:0),tex,68,24,true);return out;}
function svgStart(maxP=5,maxQ=5){layout={dx:625/maxP,dy:370/maxQ};let out=`<svg viewBox="0 0 840 525" role="img" aria-labelledby="graphTitle"><title id="graphTitle">${esc($('#sceneTitle').textContent)}；横轴第一指标，纵轴第二指标</title><defs>`;for(let [id,color] of [['h','#71e2d0'],['v','#8fbeff'],['r','#f4c876'],['continuation','#8da7ae']])out+=`<marker id="arrow-${id}" markerWidth="7" markerHeight="7" refX="6" refY="3" orient="auto"><path d="M0,0 L6,3 L0,6" fill="none" stroke="${color}"/></marker>`;out+='</defs>';for(let p=0;p<=maxP;p++){let [x]=xy(p,0);out+=`<path class="grid" d="M${x},38 V455"/><text class="axis-text" x="${x}" y="495" text-anchor="middle">${p}</text>`;}for(let qv=0;qv<=maxQ;qv++){let [,y]=xy(0,qv);out+=`<path class="grid" d="M30,${y} H${Math.min(785,xy(maxP,0)[0]+40)}"/><text class="axis-text" x="13" y="${y+5}">${qv}</text>`;}out+='<path d="M30,25 V473 H797" fill="none" stroke="#587985"/><text class="axis-text" x="806" y="480">p</text><text class="axis-text" x="13" y="25">q</text>';return out;}
function node(p,qv,tex,{dim,muted=false,active=false}={}){let [x,y]=xy(p,qv);return `<g data-concept="space" class="node ${muted?'muted':''} ${active?'trace-active':''} ${state.selected?.p===p&&state.selected?.q===qv?'selected':''} ${dim===0?'zero':''}" role="button" tabindex="0" data-p="${p}" data-q="${qv}" aria-label="位置 (${p},${qv})${dim!==undefined?`, 维数 ${dim}`:''}"><rect class="node-bg" x="${x-52}" y="${y-21}" width="104" height="42" rx="8"/>${label(x,y,tex,103,38,tex.length>28)}</g>`;}
function diagonal(n,p,box=true){if(p>n)return '';let [x1,y1]=xy(p,n-p),[x2,y2]=xy(n,0);let dx=x2-x1,dy=y2-y1,len=Math.hypot(dx,dy);if(!len){dx=125;dy=79;len=Math.hypot(dx,dy);}const ux=dx/len,uy=dy/len,vx=-uy,vy=ux;let points=[[-55,-32],[len===Math.hypot(125,79)&&p===n?55:len+55,-32],[len===Math.hypot(125,79)&&p===n?55:len+55,32],[-55,32]].map(([a,b])=>`${x1+ux*a+vx*b},${y1+uy*a+vy*b}`).join(' ');let out=box?`<polygon data-concept="filtration" class="diag-box" points="${points}"/>`:'';out+=`<path class="diag" d="M${xy(0,n).join(',')} L${xy(n,0).join(',')}"/>`;out+=label(700,17,raw`i+j=${n}`,120,24,true);return out;}
function conceptual(){let s=state.step+1,n=state.n,p=state.p,max=5,out=svgStart(max,max);if([1,2,3].includes(s))out+=diagonal(n,s===1?0:p,s!==1);let horizontal=s===0||s===1||s===2||s===5,vertical=s<=2||s===4;
for(let i=0;i<=max;i++)for(let j=0;j<=max;j++){let [x,y]=xy(i,j);if(horizontal&&i<max)out+=line(x,y,...xy(i+1,j),'h',s===5||state.direction!=='v',j===2&&i===1?(s===5?'d_1':'\\delta_1'):'');if(vertical&&j<max)out+=line(x,y,...xy(i,j+1),'v',s===4||state.direction!=='h',j===1&&i===3?'\\delta_2':'');}
if(s===6){let from=[0,3],r=2;out+=line(...xy(...from),...xy(r,4-r),'r',true,raw`d_2`);}
for(let i=0;i<=max;i++)for(let j=0;j<=max;j++){let tex=s===5?raw`H^{${j}}(K^{${i},\bullet})`:s===6?raw`E_2^{${i},${j}}`:raw`K^{${i},${j}}`;let muted=[1,2].includes(s)?(i+j!==n||(s===2&&i<p)):s===3?!(i===p&&i+j===n):false;out+=node(i,j,tex,{muted});}out+='</svg>';return out;}
function actualDiagram(){const c=scene(),r=pageR(),isTrace=state.module==='trace',maxP=Math.max(c.maxP,state.module==='converge'?state.n:0,3),maxQ=Math.max(c.maxQ,state.module==='converge'?state.n:0,2);let out=svgStart(maxP,maxQ);if(state.module==='converge'&&state.n<=4)out+=diagonal(state.n,state.p,true);
if(isTrace){for(let kind of ['h','v'])for(let [a,b,k]of c.ex[kind]){let src=c.ex.gens.find(g=>g.id===a),tar=c.ex.gens.find(g=>g.id===b),hot=state.step===0?kind==='v'&&a==='x':state.step===1?kind==='h'&&a==='b':state.step===2?kind==='v'&&a==='c':state.step===3?kind==='h'&&a==='c':false;out+=line(...xy(src.p,src.q),...xy(tar.p,tar.q),kind,hot,hot?(kind==='h'?'\\delta_1':'\\delta_2')+(k<0?'=-1':'=1'):'');}if(state.step>=4)out+=line(...xy(0,1),...xy(2,0),'r',true,'d_2');}
else for(let p=0;p<=maxP;p++)for(let qv=0;qv<=maxQ;qv++){let src=c.page(r,p,qv),tar=c.page(r,p+r,qv-r+1);if(src.dim&&tar.dim){let M=c.differential(r,p,qv);if(rank(M,tar.dim))out+=line(...xy(p,qv),...xy(p+r,qv-r+1),r===0?'v':r===1?'h':'r',true,raw`d_${r}`);}}
for(let p=0;p<=maxP;p++)for(let qv=0;qv<=maxQ;qv++){let tex,dim,active=false,muted=false;if(isTrace){let gs=c.ex.gens.filter(g=>g.p===p&&g.q===qv);dim=gs.length;tex=dim?raw`\langle ${gs.map(g=>g.id).join(',')}\rangle`:'0';active=state.step<3?(p===0&&qv===1)||(state.step===2&&p===1&&qv===0):state.step===3?(p===2&&qv===0)||(p===1&&qv===0):((p===0&&qv===1)||(p===2&&qv===0));}else{let E=c.page(r,p,qv);dim=E.dim;tex=dim===0?'0':dim===1?'\\mathbb Q':raw`\mathbb Q^{${dim}}`;if(state.module==='converge')muted=p+qv!==state.n||p<state.p;}out+=node(p,qv,tex,{dim,active,muted});}out+=`<text class="callout" x="104" y="510">${isTrace?'节点显示 K 中选定的基；未列出的空间全部为 0。':`每个节点是 ${state.module==='converge'?'E∞':`E${r}`} 中的一个向量空间；所有未列出的项为 0。`}</text></svg>`;return out;}
const formulas=(fs,concepts=[])=>fs.map((t,i)=>block(t,concepts[i]||'')).join('');
function companion(item){if(isBuilding()){buildCompanion(item);return;}const meta=statementMeta();$('#sceneKicker').textContent=sectionName();$('#sceneTitle').textContent=state.module==='initial'?'Initial data':state.module==='converge'?'Convergence':state.module==='lab'?'Examples':state.module==='trace'?'Representatives':'Induced structures';$('#explanation').innerHTML=`<article class="formal-statement"><div class="statement-heading"><span>${meta.kind}</span><span class="statement-number">${meta.number}</span></div><h3>${meta.name||item.title}</h3>${meta.intro?`<p class="formal-intro">${meta.intro}</p>`:''}${formulas(item.f,meta.concepts)}</article><div class="slide-supplement"><p>${item.text}</p><details><summary>展开数学理由</summary><p>${item.proof}</p></details></div>`;$('#sceneNote').textContent=item.note;}
function labCompanion(){let c=scene(),r=state.r;let stable=r>=c.maxP+1;companion({title:stable?`E${r}：已经稳定`:`第 ${r} 页 · ${examples[state.example].name}`,tag:'EXACT RATIONAL COMPUTATION',f:[r===0?raw`E_0^{p,q}=\operatorname{Gr}_F^pC^{p+q}\cong K^{p,q}`:raw`E_${r}^{p,q}=\frac{Z_${r}^{p,q}}{Z_{${r-1}}^{p+1,q-1}+B_{${r-1}}^{p,q}}`,raw`d_${r}:E_${r}^{p,q}\to E_${r}^{${shifted('p',r)},${shifted('q',1-r)}}`],text:examples[state.example].description+' 点击任意节点查看代表元、微分矩阵以及本位置的核和像。',note:'每个“下一页”从同一总复形的 Zᵣ、Bᵣ 商空间计算。上同调类使用 [a]ᵣ；所列基是计算选择，不是典范分裂。',proof:'计算全部在 ℚ 上进行，分数约分后精确运算。每页检验 dᵣ²=0，下一页维数等于本页核维数减去入射像维数，并独立计算总上同调。'});let summary='<table class="data-table"><tr><th>n</th><th>dim Hⁿ(C)</th><th>Σ dim E∞ᵖⁿ⁻ᵖ</th></tr>';for(let n=0;n<=c.maxN;n++){let H=c.cohomology(n).dim,sum=0;for(let p=0;p<=n;p++)sum+=c.page(c.maxP+2,p,n-p).dim;summary+=`<tr><td>${n}</td><td>${H}</td><td>${sum}</td></tr>`;}$('#explanation').insertAdjacentHTML('beforeend',summary+'</table><p class="badge">由总微分独立核对</p>');let data=c.ex.gens.map(g=>block(raw`${g.id}\in K^{${g.p},${g.q}}`)).join(''); for(let kind of ['h','v'])data+=c.ex[kind].map(([a,b,k])=>block(raw`\delta_${kind==='h'?1:2}${a}=${k===1?'':k===-1?'-':k}${b}`)).join(''); $('#explanation').insertAdjacentHTML('beforeend',`<details><summary>例子的全部生成元与微分</summary>${data}<p>每个列出的生成元为一个基向量；所有未列出的空间及微分值为零。</p></details>`);}
function traceCompanion(){const L=state.lambda,rep=L===0?'b':`b${L>0?'+':''}${L}y`;let items=[
{title:'选择同一个 E₁ 类的代表元',f:[raw`\delta_2x=y,\quad \delta_2b=0`,raw`a_0=${rep}`,raw`a_0-b=\delta_2(${L}x)`],text:'加入一个垂直边界不会改变 E₁ 中的类。调节 λ，观察 a₀=b+λy 是不同上链，却代表同一个垂直上同调类。'},
{title:'横向微分产生一个可消去的项',f:[raw`\delta_1a_0=u`,raw`u=-\delta_2c`,raw`d_1[a_0]=[u]=0`],text:'δ₁a₀ 本身不为零，但它是垂直边界，因此在 E₁ 上为零。该类是 d₁-闭的。'},
{title:'加入修正项 a₁=c',f:[raw`a_1=c\in K^{1,0}`,raw`\delta_1a_0+\delta_2a_1=u-u=0`],text:'修正项 c 向右一列、向下一行，总次数保持为 1。它抵消了 D(a₀) 在第一列中的分量。'},
{title:'总微分只剩右边第二列',f:[raw`a=a_0+a_1=${rep}+c`,raw`Da=z\in K^{2,0}`],text:'施加的始终是 D=δ₁+δ₂。抵消之后，残余项位于相隔两列的位置，给出了第二微分。'},
{title:'得到非零的 d₂',f:[raw`d_2:E_2^{0,1}\to E_2^{2,0}`,raw`d_2[a_0+c]_2=[z]_2\ne0`],text:'源和靶都是一维空间，d₂ 是同构。这里 [a₀+c]₂ 是总上链代表元在第二页商空间中的类。'},
{title:'第三页：两个类都不再贡献',f:[raw`E_3^{0,1}=E_3^{2,0}=0`,raw`H^*(C,D)=0`],text:'源上的类不是 d₂-闭的；靶上的类是 d₂-边界。它们以不同原因在下一页为零，不能笼统理解为两个点被动画删除。'}];let item=items[state.step];companion({...item,tag:'FOLLOW A REPRESENTATIVE',note:'本模块使用 d₂ 例子，另加 x→y 的垂直可缩复形。改变 λ 只改变代表元，不改变各页或最终答案。',proof:'新增生成元 x∈K⁰⁰、y∈K⁰¹ 满足 δ₂x=y，其余涉及 x、y 的微分为零。因此它们组成一个垂直可缩直和因子，既不改变 E₁ 及后续各页，也不改变总上同调。'});}
function convergenceTable(){let c=scene(),n=state.n,p=state.p,r=c.maxP+2,fp=c.filtration(n,p),fp1=c.filtration(n,p+1),dim=c.page(r,p,n-p).dim;$('#explanation').insertAdjacentHTML('beforeend',`<table class="data-table"><tr><th>对象</th><th>维数</th></tr><tr><td>${math(raw`F^{${p}}H^{${n}}`)}</td><td>${fp}</td></tr><tr><td>${math(raw`F^{${p+1}}H^{${n}}`)}</td><td>${fp1}</td></tr><tr><td>${math(raw`\operatorname{Gr}_F^{${p}}H^{${n}}`)}</td><td>${fp-fp1}</td></tr><tr><td>${math(raw`E_\infty^{${p},${n-p}}`)}</td><td>${dim}</td></tr></table>`);}
function inspect(){if(state.module==='learn'&&state.step===0){$('#inspector').innerHTML=block(raw`\operatorname{im}(D:C^{n-1}\to C^n)\subseteq\ker(D:C^n\to C^{n+1})`)+block(raw`[a]_H=[a+Db]_H`);return;}if(state.module==='initial'){$('#inspector').innerHTML=block(raw`K^{p,q}\xrightarrow{\delta_1}K^{p+1,q}`)+block(raw`K^{p,q}\xrightarrow{\delta_2}K^{p,q+1}`)+'<p>图中 p、q 是一般指标；虚线延续箭头表示还有未展开的行列，不表示零空间。</p>';return;}const {p,q:qv}=state.selected||{p:['learn','converge'].includes(state.module)?state.p:0,q:['learn','converge'].includes(state.module)?state.n-state.p:1};if(state.module==='learn'){let s=state.step+1,tex=raw`K^{${p},${qv}}`;let text=`第一指标为 ${p}，第二指标为 ${qv}，总次数为 ${p+qv}。`;if(s===3){tex=raw`E_0^{${p},${qv}}\cong K^{${p},${qv}}`;text+=' 同构由取该列分量给出。';}if(s===5){tex=raw`E_1^{${p},${qv}}=H^{${qv}}(K^{${p},\bullet},\delta_2)`;text+=' 这里已经对垂直方向求过上同调。';}if(s===6){tex=raw`E_r^{${p},${qv}}`;text+=' 微分靶为 (p+r,q−r+1)。';}$('#inspector').innerHTML=block(tex)+`<p>${text}</p>`;return;}
const c=scene();if(state.module==='trace'){let gs=c.ex.gens.filter(g=>g.p===p&&g.q===qv);$('#inspector').innerHTML=block(raw`K^{${p},${qv}}=\langle ${gs.map(g=>g.id).join(',')||'0'}\rangle`)+`<p>图中节点是该位置的整个空间；方程中的 b、c、x、y、u、z 是选定基向量。</p>`;return;}
let r=pageR(),E=c.page(r,p,qv),tar=c.page(r,p+r,qv-r+1),M=c.differential(r,p,qv),incoming=c.differential(r,p-r,qv+r-1),outRank=rank(M,tar.dim),inRank=rank(incoming,E.dim),name=state.module==='converge'?'\\infty':r;
let html=block(raw`E_{${name}}^{${p},${qv}}\cong\mathbb Q^{${E.dim}}`);if(E.dim)html+=`<p>选定的商空间基（总上链代表元）：</p>`+E.reps.map(v=>block(raw`[${texVector(v,c.basis(E.n))}]_{${name}}`)).join('');html+=`<p>分子维数 ${E.Z.length}；分母维数 ${E.den.length}。商空间维数 ${E.dim}。</p>`;
if(state.module==='lab'){html+=`<p>微分矩阵：列对应上面的源基，行对应靶的商空间基。</p>`+block(raw`[d_${r}]=${matrixTex(M,tar.dim)}`);html+=`<p>靶位置 (${p+r},${qv-r+1})。靶基：</p>`+block(tar.reps.length?tar.reps.map(v=>raw`[${texVector(v,c.basis(tar.n))}]_${r}`).join(',\;'):raw`\varnothing`);html+=`<p>dim ker d${r} = ${E.dim-outRank}<br>dim im（入射 d${r}）= ${inRank}<br>下一页本位置维数 = ${E.dim-outRank-inRank}</p>`;}else if(E.dim){html+=block(raw`\theta([a]_\infty)=[a]_H+F^{${p+1}}H^{${E.n}}`);}$('#inspector').innerHTML=html;}
function controls(){let html='';if(state.module==='converge'||(state.module==='learn'&&state.step>=1&&state.step<=2)){html+=`<label>示例总次数 n <input id="nRange" type="range" min="0" max="4" value="${state.n}"><output>${state.n}</output></label><label>滤过 p <input id="pRange" type="range" min="0" max="${state.n+1}" value="${state.p}"><output>${state.p}</output></label>`;}if(state.module==='initial'&&state.step>0){html+=`<div role="group" aria-label="突出箭头方向"><button data-direction="h" class="${state.direction==='h'?'active':''}" aria-pressed="${state.direction==='h'}">横向 δ₁</button> <button data-direction="v" class="${state.direction==='v'?'active':''}" aria-pressed="${state.direction==='v'}">纵向 δ₂</button> <button data-direction="both" class="${state.direction==='both'?'active':''}" aria-pressed="${state.direction==='both'}">两者</button></div>`;}if(state.module==='lab'||state.module==='converge'){html+=`<label>例子 <select id="exampleSelect">${Object.entries(examples).map(([k,e])=>`<option value="${k}" ${k===state.example?'selected':''}>${e.name}</option>`).join('')}</select></label>`;}if(state.module==='lab')html+=`<label>页数 r <input id="rRange" type="range" min="0" max="${scene().maxP+2}" value="${state.r}"><output>${state.r}</output></label>`;if(state.module==='trace')html+=`<label>代表元参数 λ <input id="lambdaRange" type="range" min="-2" max="2" value="${state.lambda}"><output>${state.lambda}</output></label><span>${math(raw`a_0=b+\lambda y`)}</span>`;let old=$('#speed')?.value;$('#controls').innerHTML=html;if(old&&$('#speed'))$('#speed').value=old;}
function render(updateControls=true){if(state.module==='initial')companion(initial[state.step]);if(state.module==='learn')companion(state.step===0?totalCohomology:lessons[state.step+1]);if(state.module==='lab')labCompanion();if(state.module==='trace')traceCompanion();if(state.module==='converge'){companion(convergence[state.step]);convergenceTable();}$('.inspector .mini-label').textContent=state.module==='initial'?'图示与记号':state.module==='learn'&&state.step===0?'闭链与边界':'点击图中的项，查看其含义';$('.legend').innerHTML=state.module==='initial'?'<span><i class="h"></i>横向 δ₁</span><span><i class="v"></i>纵向 δ₂</span>'+ (state.step===1?'<span><i class="degree"></i>选中的总次数</span>':''):state.module==='learn'&&state.step===0?'<span><i class="degree"></i>总微分 D</span>':'<span><i class="h"></i>横向 δ₁ / d₁</span><span><i class="v"></i>纵向 δ₂ / d₀</span><span><i class="degree"></i>选中的总次数</span>';$('#panelIndex').textContent=String(state.step+1).padStart(2,'0');$('#diagram').innerHTML=state.module==='initial'?initialDiagram():state.module==='learn'?(state.step===0?cohomologyDiagram():state.step===5?filteredPageDiagram():conceptual()):state.module==='converge'&&state.step>=2?comparisonDiagram():actualDiagram();if(updateControls)controls();inspect();$('#stepReadout').textContent=`${state.step+1} / ${stepCount()}`;$('#prev').disabled=state.step===0;$('#next').disabled=state.step===stepCount()-1;$('#stepTrack').innerHTML=Array.from({length:stepCount()},(_,i)=>`<button data-step="${i}" class="${i===state.step?'active':''}" aria-label="转到第 ${i+1} 步" ${i===state.step?'aria-current="step"':''}></button>`).join('');$('#play').textContent=state.playing?'Ⅱ 暂停':'▶ 播放步骤';$('#play').setAttribute('aria-pressed',state.playing);document.querySelectorAll('[data-module]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.module===state.module));const section=state.module==='initial'?'initial':state.module==='converge'?'converge':'induced';document.querySelectorAll('[data-section]').forEach(b=>b.setAttribute('aria-pressed',b.dataset.section===section));$('#submodules').hidden=section!=='induced';renderSlideState();translatePage();window.spectralState={...state,language:language()};}
function stop(){state.playing=false;clearTimeout(timer);timer=null;}
function move(i){state.cover=false;state.reveal=0;state.buildStep=0;state.pinned=null;state.step=Math.max(0,Math.min(stepCount()-1,i));if(state.module==='lab')state.r=state.step;state.selected=null;render();}
function schedule(){timer=setTimeout(()=>{if(state.step>=stepCount()-1){stop();render();return;}move(state.step+1);schedule();},Number($('#speed').value));}
function moduleChange(m){stop();state.cover=false;state.reveal=0;state.buildStep=0;state.pinned=null;state.module=m;state.step=0;state.r=0;state.selected=null;if(m==='converge'){state.example='survive';state.n=1;state.p=1;}location.hash=m;render();}
$('#prev').onclick=()=>{stop();retreatSlide();};$('#next').onclick=()=>{stop();advanceSlide();};$('#play').onclick=()=>{};
$('#beginSlides').onclick=()=>{state.cover=false;state.reveal=0;state.buildStep=0;render();};$('#coverButton').onclick=()=>{stop();state.module='initial';state.step=0;state.cover=true;state.reveal=0;state.buildStep=0;state.pinned=null;location.hash='title';render();};
document.querySelector('.module-dock').onclick=e=>{let b=e.target.closest('[data-section]');if(b)moduleChange(b.dataset.section==='induced'?'learn':b.dataset.section);};$('#submodules').onclick=e=>{let b=e.target.closest('[data-module]');if(b)moduleChange(b.dataset.module);};$('#stepTrack').onclick=e=>{let b=e.target.closest('[data-step]');if(e.target.closest('[data-cover]')){$('#coverButton').click();return;}if(b){stop();move(Number(b.dataset.step));}};
$('#controls').addEventListener('input',e=>{let id=e.target.id;if(!id.endsWith('Range'))return;stop();const val=Number(e.target.value);if(id==='nRange'){state.n=val;state.p=Math.min(state.p,val+1);$('#pRange').max=val+1;$('#pRange').value=state.p;$('#pRange').nextElementSibling.textContent=state.p;}if(id==='pRange')state.p=val;if(id==='lambdaRange')state.lambda=val;if(id==='rRange'){state.r=val;state.step=val;}e.target.nextElementSibling.textContent=val;state.selected=null;render(false);});
$('#controls').onchange=e=>{if(e.target.id==='exampleSelect'){stop();state.example=e.target.value;state.r=0;state.step=0;state.selected=null;render();}};
$('#controls').onclick=e=>{let b=e.target.closest('[data-direction]');if(b){state.direction=b.dataset.direction;render();}};
function selectNode(e){let b=e.target.closest('[data-p]');if(b){state.selected={p:Number(b.dataset.p),q:Number(b.dataset.q)};render(false);}}$('#diagram').onclick=selectNode;$('#diagram').onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();const el=e.target.closest('[data-concept]');if(el)pinConcept(el.dataset.concept);selectNode(e);}};
let fullscreenScroll=0;
function syncFullscreenButton(){const active=document.body.classList.contains('study-fullscreen');$('#fullscreen').textContent=active?'⛶ 退出全屏':'⛶ 全屏';$('#fullscreen').title=active?'退出全屏（Esc）':'全屏显示工作区';$('#fullscreen').setAttribute('aria-pressed',String(active));translatePage();}
function leaveFocusMode(){document.body.classList.remove('study-fullscreen');syncFullscreenButton();window.scrollTo(0,fullscreenScroll);$('#fullscreen').focus({preventScroll:true});}
async function exitStudyFullscreen(){if(document.fullscreenElement){try{await document.exitFullscreen();}catch{}}leaveFocusMode();}
$('#fullscreen').onclick=async()=>{if(document.body.classList.contains('study-fullscreen')){await exitStudyFullscreen();return;}fullscreenScroll=window.scrollY;document.body.classList.add('study-fullscreen');syncFullscreenButton();try{if(document.documentElement.requestFullscreen)await document.documentElement.requestFullscreen();}catch{/* Embedded browsers retain the viewport-filling focus mode. */}};
document.addEventListener('fullscreenchange',()=>{if(!document.fullscreenElement&&document.body.classList.contains('study-fullscreen'))leaveFocusMode();});
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&document.body.classList.contains('study-fullscreen')&&!$('#formulaDialog').open&&!$('#references').open){e.preventDefault();exitStudyFullscreen();}});
$('#proofJump').onclick=()=>{moduleChange('converge');$('.workspace').scrollIntoView({behavior:'smooth'});};
const refHTML=`<p>本主题采用 McCleary《A User’s Guide to Spectral Sequences》第二版的上同调型记号，保留讲义的 K、δ₁、δ₂。滤过固定为按列的下降滤过。</p>${formulas([raw`D=\delta_1+\delta_2,\quad \delta_1\delta_2+\delta_2\delta_1=0`,raw`E_0^{p,q}=\operatorname{Gr}_F^pC^{p+q}\cong K^{p,q}`,raw`E_r^{p,q}=Z_r^{p,q}/(Z_{r-1}^{p+1,q-1}+B_{r-1}^{p,q})`,raw`d_r:E_r^{p,q}\to E_r^{p+r,q-r+1}`,raw`E_\infty^{p,q}\cong\operatorname{Gr}_F^pH^{p+q}`])}<p><b>记号界限：</b>δ₁、δ₂ 是双复形微分；d₀、d₁、… 是页上的微分。Zᵣ、Bᵣ 是总复形中的子空间；[a]ᵣ 是 Eᵣ 的类，[a]H 是总上同调类。动画中示意空间的大小不代表维数。</p><p><b>有限例子：</b>给定全部生成元和箭头，其余项确实为零。基、矩阵与代表元来自精确有理数消元；选择这些基不赋予 H 的滤过一个典范分裂。</p><p><b>阅读依据：</b>Definition 2.2（谱序列）、Definitions 2.3–2.5（滤过与收敛）、Theorem 2.6 及证明（pp. 33–37）、Theorem 2.15（双复形，pp. 48–49）。</p><p><a href="https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/McCleary-UGSS.pdf" target="_blank" rel="noreferrer">打开 McCleary 原书 ↗</a> · <a href="spectral.pdf">打开本主题讲义 ↗</a></p><p>键盘：← / → 和空格逐步展开或翻页。符号支持 Tab 聚焦与 Enter 固定高亮；公式右上角可放大。选择框和滑块保留自身的键盘行为。</p>`;
$('#referenceContent').innerHTML=refHTML;$('#referenceButton').onclick=()=>{translatePage();$('#references').showModal();};$('#closeReferences').onclick=()=>$('#references').close();
document.addEventListener('keydown',e=>{if($('#references').open||$('#formulaDialog').open||e.target.closest('[data-formula],.build-card')||['INPUT','SELECT','BUTTON','A'].includes(document.activeElement.tagName))return;if(e.key==='ArrowRight')$('#next').click();if(e.key==='ArrowLeft')$('#prev').click();if(e.code==='Space'){e.preventDefault();$('#next').click();}});
document.addEventListener('visibilitychange',()=>{if(document.hidden){stop();render(false);}});
window.addEventListener('hashchange',()=>{let m=location.hash.slice(1);if(m==='title'&&!state.cover){$('#coverButton').click();return;}if(['initial','learn','lab','trace','converge'].includes(m)&&m!==state.module)moduleChange(m);});
document.querySelectorAll('[data-tex]').forEach(el=>el.innerHTML=math(el.dataset.tex));
if(['initial','learn','lab','trace','converge'].includes(location.hash.slice(1))){state.module=location.hash.slice(1);state.cover=false;}
$('#languageButton').onclick=()=>{toggleLanguage();render();};
render();

function openFormula(e){const el=e.target.closest('[data-formula]');if(!el||el.closest('#formulaDialog')||(el.dataset.concept&&!e.target.closest('[data-zoom]')))return;$('#formulaContent').innerHTML=math(el.dataset.formula,true);$('#formulaDialog').showModal();}
document.addEventListener('click',openFormula);
document.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('[data-formula]')){e.preventDefault();if(e.target.dataset.concept)pinConcept(e.target.dataset.concept);else openFormula(e);}});
$('#closeFormula').onclick=()=>$('#formulaDialog').close();

function initialDiagram(){
 let out=svgStart(5,5);out=out.slice(0,out.indexOf('</defs>')+7);
 const edge=(x1,y1,x2,y2,...args)=>{const dx=x2-x1,dy=y2-y1,l=Math.hypot(dx,dy),pad=14;return line(x1+pad*dx/l,y1+pad*dy/l,x2-pad*dx/l,y2-pad*dy/l,...args);};
 const box=(x,y,t)=>`<g data-concept="space" tabindex="0" role="button" aria-label="${esc(t)}"><rect class="node-bg schematic-node" x="${x-65}" y="${y-24}" width="130" height="48" rx="8"/>`+label(x,y,t,128,42)+'</g>';
 if(state.step===0){
 const xs=[100,290,480,690],ys=[430,310,190,70],ps=['0','1','p','p+1'],qs=['0','1','q','q+1'];
 for(let i=0;i<4;i++)for(let j=0;j<4;j++){
  if(i!==1&&i<3)out+=buildLayer(1,edge(xs[i],ys[j],xs[i+1],ys[j],'h',state.direction!=='v',j===2?'\\delta_1':''));
  if(j!==1&&j<3)out+=buildLayer(2,edge(xs[i],ys[j],xs[i],ys[j+1],'v',state.direction!=='h',i===2?'\\delta_2':''));
 }
 if(isBuilding())out+=buildLayer(4,'<rect class="relation-square" x="457" y="47" width="256" height="166" rx="9"/>');
 for(let i=0;i<4;i++)for(let j=0;j<4;j++)out+=box(xs[i],ys[j],`K^{${ps[i]},${qs[j]}}`);
 for(let y of ys)out+=buildLayer(1,continuation(363,y,407,y,'delta1'));
 for(let x of xs)out+=buildLayer(2,continuation(x,278,x,222,'delta2'));

 for(let y of ys)out+=buildLayer(1,continuation(767,y,818,y,'delta1'));for(let x of xs)out+=buildLayer(2,continuation(x,36,x,7,'delta2'));
 if(isBuilding())out+=buildLayer(3,label(265,491,'\\delta_1^2=\\delta_2^2=0',300,34))+buildLayer(4,label(630,491,'\\delta_1\\delta_2+\\delta_2\\delta_1=0',365,34));
 out+=`<text class="callout" x="100" y="503">${state.step===0?'每个 Kᵖᑫ 是向量空间；虚线延续箭头表示未展开的行列。':'只在相邻指标之间画 δ 箭头；两条复合路径之和为零。'}</text>`;
 }else{
 const pts=[[95,120,'0,n'],[280,220,'1,n-1'],[550,366,'n-1,1'],[735,466,'n,0']];
 out+='<path class="diag" d="M95,120 L280,220 M550,366 L735,466"/>';
 for(let [x,y,t] of pts)out+=box(x,y,`K^{${t}}`);
 out+=continuation(347,256,483,330,'total');
 out+=label(650,30,'i+j=n',150,34);
 out+=label(595,80,'C^n=\\bigoplus_{i=0}^{n}K^{i,n-i}',360,46);
 out+=edge(280,220,490,220,'h',state.direction!=='v','\\delta_1');
 out+=edge(280,220,280,70,'v',state.direction!=='h','\\delta_2');
 out+=box(490,220,'K^{2,n-1}');out+=box(280,70,'K^{1,n}');
 out+=label(660,185,'i+j=n+1',160,34);
 out+=`<text class="callout" x="95" y="500">两种微分都把总次数提高一；图以 n ≥ 3 的一般情形示意。</text>`;
 }
 return out+'</svg>';
}

function cohomologyDiagram(){
 let out=svgStart();out=out.slice(0,out.indexOf('</defs>')+7);
 out+=continuation(40,105,135,105,'differential')+label(205,105,'C^{n-1}',100,40)+label(420,105,'C^n',100,40)+label(635,105,'C^{n+1}',100,40)+continuation(705,105,803,105,'differential');
 out+=line(205,105,420,105,'r',true,'D')+line(420,105,635,105,'r',true,'D');
 out+='<rect x="175" y="180" width="490" height="265" rx="20" fill="#102630" stroke="#42616b"/><rect data-concept="cycles" class="cohomology-region" x="210" y="240" width="420" height="175" rx="18" fill="#14362f" stroke="#71e2d0"/><rect data-concept="boundaries" class="cohomology-region" x="245" y="315" width="350" height="70" rx="15" fill="#263747" stroke="#8fbeff"/>';
 out+=label(420,209,'C^n',190,40)+label(420,271,'Z^n=\\ker(D:C^n\\to C^{n+1})',380,40)+label(420,350,'B^n=\\operatorname{im}(D:C^{n-1}\\to C^n)',340,40);
 out+=label(420,482,'H^n(C,D)=Z^n/B^n',450,40);return out+'</svg>';
}

function sectionName(){return state.module==='initial'?'01 / INITIAL DATA':state.module==='converge'?'03 / CONVERGENCE':'02 / INDUCED STRUCTURES';}
function statementMeta(){
 const collections={
 initial:[
 {kind:'定义',number:'1.1',name:'双复形',intro:'在上述双分次向量空间上给定以下线性映射，并要求它们满足所列恒等式。',concepts:['delta1','delta2','differential','differential']},
 {kind:'定义',number:'1.2',name:'总复形',intro:'对每个总次数 n，将同一条对角线上的空间取直和，并定义总微分。',concepts:['total','differential','differential']}
 ],
 learn:[
 {kind:'定义',number:'2.1',name:'上同调',concepts:['cohomology','boundaries']},
 {kind:'定义',number:'2.2',name:'列滤过',concepts:['filtration','filtration','differential']},
 {kind:'定义',number:'2.3',name:'关联分次与第零页',concepts:['quotient','quotient','space']},
 {kind:'命题',number:'2.4',name:'第零微分与第一页',concepts:['delta2','cohomology','cohomology']},
 {kind:'命题',number:'2.5',name:'第一微分与第二页',concepts:['delta1','delta1','quotient']},
 {kind:'定义',number:'2.6',name:'滤过闭链、边界与一般页',concepts:['cycles','boundaries','page','differential']}
 ],
 converge:[
 {kind:'定义',number:'3.1',name:'上同调上的诱导滤过',concepts:['cohomology','filtration','quotient']},
 {kind:'引理',number:'3.2',name:'有界性与稳定',intro:'令 n=p+q，并保留第一象限假设。',concepts:['filtration','cycles','boundaries']},
 {kind:'命题',number:'3.3',name:'典范比较映射',concepts:['page','comparison','comparison']},
 {kind:'定理',number:'3.4',name:'有界滤过的收敛',concepts:['filtration','cycles','comparison','boundaries','comparison']},
 {kind:'解释与结论',number:'3.5',name:'收敛的意义',concepts:['comparison','filtration']}
 ]};
 return collections[state.module]?.[state.step]||{kind:state.module==='lab'?'例':'计算',number:`2.${state.module==='lab'?'7':'8'}.${state.step+1}`,concepts:state.module==='lab'?['page','differential']:['differential','space','differential']};
}
function arrowConcept(type){return type==='h'?'delta1':type==='v'?'delta2':'differential';}
function renderSlideState(){
 const deck=$('.slide-deck'),cover=state.cover;
 deck.classList.toggle('is-building',isBuilding());deck.classList.toggle('is-cover',cover);deck.classList.toggle('has-diagram',!cover&&state.reveal>=1);deck.classList.toggle('has-explanation',!cover&&state.reveal>=2);deck.dataset.fragment=String(state.reveal);
 $('#slideCover').hidden=!cover;$('.slide-body').inert=cover;$('#visualPanel').inert=cover||state.reveal===0;
 if(cover){$('#sceneKicker').textContent='STUDY ATLAS / AT·002';$('#sceneTitle').textContent='';}
 const pages=stepCount()+(state.module==='initial'?1:0),page=cover?1:state.step+1+(state.module==='initial'?1:0);
 $('#stepReadout').textContent=`${String(page).padStart(2,'0')} / ${String(pages).padStart(2,'0')}`;
 $('#prev').disabled=cover;$('#next').disabled=!cover&&state.module==='converge'&&state.step===stepCount()-1&&state.reveal===2;
 $('#next').textContent=cover?'开始阅读 →':state.reveal===0?'显示图示 →':state.reveal===1?'展开解释 →':'下一页 →';
 $('#fragmentTrack').innerHTML=cover?'<span>DEFINITIONS → CONVERGENCE</span>':['陈述','图示','解释'].map((t,i)=>`<button data-fragment="${i}" aria-pressed="${state.reveal===i}" class="${i<=state.reveal?'seen':''}">${t}</button>`).join('<i></i>');
 $('#stepTrack').innerHTML=(state.module==='initial'?`<button data-cover title="标题页" class="${cover?'active':''}" aria-label="标题页"></button>`:'')+Array.from({length:stepCount()},(_,i)=>`<button data-step="${i}" class="${!cover&&i===state.step?'active':''}" aria-label="转到第 ${i+1} 步" title="${esc((state.module==='initial'?initial:state.module==='converge'?convergence:[])[i]?.title||String(i+1))}"></button>`).join('');
 if($('#diagram .continuation'))$('.legend').insertAdjacentHTML('beforeend','<span><i class="continuation-key"></i>虚线：中间项省略</span>');
 $('#sceneNote').hidden=cover||state.reveal<2;
 renderQuickCheck();if(isBuilding())setupBuild();applyConcept(state.pinned,false);
}
function advanceSlide(){
 if(isBuilding()){if(state.buildStep<4)setBuildStep(state.buildStep+1);else move(state.step+1);return;}
 if(state.cover){state.cover=false;state.reveal=0;render();return;}
 if(state.reveal<2){state.reveal++;render();return;}
 if(state.step<stepCount()-1){move(state.step+1);return;}
 const next={initial:'learn',learn:'converge',lab:'trace',trace:'converge'}[state.module];if(next)moduleChange(next);
}
function retreatSlide(){
 if(isBuilding()&&state.buildStep>0){setBuildStep(state.buildStep-1);return;}
 if(state.reveal>0){state.reveal--;render();return;}
 if(state.step>0){move(state.step-1);state.reveal=2;render();return;}
 if(state.module==='initial')$('#coverButton').click();else{moduleChange(state.module==='converge'?'learn':'initial');state.step=stepCount()-1;state.reveal=2;render();}
}
$('#fragmentTrack').onclick=e=>{const build=e.target.closest('[data-build-to]');if(build){setBuildStep(Number(build.dataset.buildTo));return;}const b=e.target.closest('[data-fragment]');if(b){state.reveal=Number(b.dataset.fragment);render();}};
function relatedConcept(a,b){if(a===b)return true;const groups=[['space','page','quotient'],['delta1','differential'],['delta2','differential'],['comparison','page'],['total','filtration']];return groups.some(g=>g.includes(a)&&g.includes(b));}
function applyConcept(concept,hover=false){
 const graph=$('#diagram');graph.querySelectorAll('.concept-active').forEach(el=>el.classList.remove('concept-active'));
 graph.classList.toggle('concept-focus',!!concept);graph.classList.toggle('hover-effect',!!concept&&hover);
 const targets={delta1:'.arrow.h,.continuation[data-concept=delta1]',delta2:'.arrow.v,.continuation[data-concept=delta2]',differential:'.arrow,.continuation[data-concept=delta1],.continuation[data-concept=delta2],.continuation[data-concept=differential]',space:'.node-bg',page:'.node-bg,.comparison-node,.page-quotient',quotient:'.node:not(.muted) .node-bg',total:'.diag,.node:not(.muted) .node-bg,.continuation[data-concept=total]',filtration:'.diag-box,.node:not(.muted) .node-bg',cycles:'[data-concept=cycles]',boundaries:'[data-concept=boundaries]',cohomology:'.cohomology-region,.node-bg',comparison:'.comparison-node,.comparison-arrow,.node:not(.zero) .node-bg,.diag-box'};
 if(concept)graph.querySelectorAll(targets[concept]||'[data-concept]').forEach(el=>el.classList.add('concept-active'));
 document.querySelectorAll('.formal-statement [data-concept]').forEach(el=>{el.classList.toggle('concept-linked',!!concept&&relatedConcept(concept,el.dataset.concept));el.setAttribute('aria-pressed',String(state.pinned===el.dataset.concept));});
 $('#clearConcept').hidden=!state.pinned;
}
function pinConcept(concept){state.pinned=state.pinned===concept?null:concept;applyConcept(state.pinned,false);translatePage();window.spectralState={...state,language:language()};}
function interactiveConcept(target){return target.closest('.formal-statement [data-concept],#diagram [data-concept]');}
document.addEventListener('pointerover',e=>{const el=interactiveConcept(e.target);if(el&&!el.contains(e.relatedTarget)){revealBuildFor(el);applyConcept(el.dataset.concept,true);}});
document.addEventListener('pointerout',e=>{const el=interactiveConcept(e.target);if(el&&!el.contains(e.relatedTarget))applyConcept(state.pinned,false);});
document.addEventListener('focusin',e=>{const el=interactiveConcept(e.target);if(el){revealBuildFor(el);applyConcept(el.dataset.concept,true);}});
document.addEventListener('focusout',e=>{const el=interactiveConcept(e.target);if(el&&!el.contains(e.relatedTarget))applyConcept(state.pinned,false);});
document.addEventListener('click',e=>{const el=interactiveConcept(e.target);if(el&&!e.target.closest('[data-zoom]')){revealBuildFor(el);pinConcept(el.dataset.concept);}});
$('#clearConcept').onclick=()=>{state.pinned=null;applyConcept(null);};

function comparisonDiagram(){
 let out=svgStart();out=out.slice(0,out.indexOf('</defs>')+7);
 for(const x of [205,635])out+=`<rect data-concept="comparison" class="node-bg comparison-node" tabindex="0" role="button" x="${x-148}" y="120" width="296" height="110" rx="10"/>`;
 out+=label(205,175,'E_\\infty^{p,q}',230,65)+label(635,175,'\\operatorname{Gr}_F^p H^{p+q}',270,65);
 out+=`<path data-concept="comparison" class="arrow r comparison-arrow" tabindex="0" role="button" d="M365,175 L473,175" marker-end="url(#arrow-r)"/>`;
 out+=label(420,140,'\\theta^{p,q}',100,40);
 out+=label(205,310,'[a]_\\infty',230,65)+label(635,310,'[a]_H+F^{p+1}H^{p+q}',300,65);
 out+='<path data-concept="comparison" class="arrow r comparison-arrow" tabindex="0" role="button" d="M300,310 L450,310" marker-end="url(#arrow-r)"/><path d="M300,300 V320" stroke="#f4c876" fill="none"/>';
 out+=label(420,414,'a\\in F^pC^{p+q},\\qquad Da=0',600,55);
 out+=label(420,460,'\\ker(Z_\\infty^{p,q}\\to\\operatorname{Gr}_F^pH^{p+q})',710,38);out+=label(420,498,'=Z_\\infty^{p+1,q-1}+B_\\infty^{p,q}',600,32);return out+'</svg>';
}

function filteredPageDiagram(){
 let out=svgStart();out=out.slice(0,out.indexOf('</defs>')+7);
 out+=label(710,24,'n=p+q',170,35);
 const region=(x,y,c,tex)=>`<rect data-concept="${c}" class="node-bg subspace-region" tabindex="0" role="button" x="${x-157}" y="${y-48}" width="314" height="96" rx="8"/>`+label(x,y,tex,302,80);
 out+=region(205,125,'cycles','a\\in Z_r^{p,q}\\subseteq F^pC^n')+region(635,125,'cycles','Da\\in F^{p+r}C^{n+1}');
 out+=region(205,300,'boundaries','\\substack{c\\in F^{p-r}C^{n-1}\\\\ Dc\\in F^pC^n}')+region(635,300,'boundaries','b=Dc\\in B_r^{p,q}');
 for(const y of [125,300]){out+=`<path data-concept="differential" class="arrow r" tabindex="0" role="button" d="M375,${y} L462,${y}" marker-end="url(#arrow-r)"/>`+label(420,y-30,'D',80,35);}
 out+='<rect data-concept="page" class="node-bg page-quotient" tabindex="0" role="button" x="40" y="405" width="760" height="108" rx="8"/>';
 out+=label(420,459,lessons[6].f[2],735,100);return out+'</svg>';
}
function renderQuickCheck(){
 const checks={initial:['如果先作用 δ₂，再作用 δ₁，终点在哪里？','终点是 Kᵖ⁺¹ᑫ⁺¹。交换作用顺序仍到同一位置，但两条复合映射之和为零。'],learn:['dᵣ 的靶在哪里？总次数改变多少？','靶是 Eᵣᵖ⁺ʳ,ᑫ⁻ʳ⁺¹，因此总次数从 p+q 变成 p+q+1。'],converge:['稳定页是否给出了 Hⁿ 的典范直和分解？','没有。它典范地给出滤过商 GrᵖHⁿ。向量空间层面的分裂可以选择，但收敛本身不指定典范分裂。']};
 const entry=checks[state.module],el=$('#quickCheck');el.hidden=!entry||state.cover||state.reveal<2||state.step!==stepCount()-1;
 el.innerHTML=entry?`<summary><span>自检</span> · <span>${entry[0]}</span></summary><p>${entry[1]}</p>`:'';
}

function continuation(x1,y1,x2,y2,concept=''){const marker=concept==='delta1'?'h':concept==='delta2'?'v':concept==='total'||concept==='differential'?'r':'continuation';return `<path class="continuation" ${concept?`data-concept="${concept}" tabindex="0"`:''} d="M${x1},${y1} L${x2},${y2}" marker-end="url(#arrow-${marker})" role="${concept?'button':'img'}" aria-label="延续箭头：省略中间项，不表示一次微分"><title>延续箭头：省略中间项，不表示一次微分</title></path>`;}

function isBuilding(){return !state.cover&&state.module==='initial'&&state.step===0;}
function buildLayer(level,html){return isBuilding()?`<g class="build-layer" data-build-level="${level}">${html}</g>`:html;}
function buildCompanion(item){
 $('#sceneKicker').textContent=sectionName();$('#sceneTitle').textContent='Initial data';
 const cards=[
 {title:'横向微分 δ₁',concept:'delta1',text:'第一指标增加 1，第二指标保持不变。固定 q，沿同一行向右。'},
 {title:'纵向微分 δ₂',concept:'delta2',text:'第二指标增加 1，第一指标保持不变。固定 p，沿同一列向上。'},
 {title:'各方向的平方为零',concept:'differential',text:'沿同一方向连续作用两次，复合映射为零。因此每行、每列分别是上链复形。'},
 {title:'两个方向反交换',concept:'differential',text:'右上方小方格的两条复合路径有相同的终点，但对应映射互为相反数。'}
 ];
 $('#explanation').innerHTML=`<article class="formal-statement build-statement"><div class="statement-heading"><span>定义</span><span class="statement-number">1.1</span></div><h3>双复形</h3><p class="formal-intro">设 Kᵖᑫ 为 ℚ-向量空间，且当 p<0 或 q<0 时为零。依次加入以下微分与关系。</p>${cards.map((c,i)=>`<section class="build-card" data-build="${i+1}" data-concept="${c.concept}" tabindex="0" role="button"><h4><span class="build-number">${String(i+1).padStart(2,'0')}</span><span>${c.title}</span></h4>${block(item.f[i],c.concept)}<p>${c.text}</p></section>`).join('')}</article>`;
 $('#sceneNote').textContent='悬停或点击左侧的下一项，逐步添加图中的元素。也可使用下方按钮。';
}
function setupBuild(){
 const deck=$('.slide-deck');deck.classList.add('has-diagram');deck.classList.remove('has-explanation');$('#visualPanel').inert=false;$('#sceneNote').hidden=false;
 $('#fragmentTrack').innerHTML=['空间','δ₁','δ₂','平方为零','反交换'].map((t,i)=>`<button data-build-to="${i}" aria-pressed="${state.buildStep===i}">${t}</button>`).join('<i></i>');
 updateBuildDOM();
}
function updateBuildDOM(){
 const level=state.buildStep;$('.slide-deck').dataset.buildStep=String(level);
 document.querySelectorAll('.build-layer').forEach(el=>{const shown=Number(el.dataset.buildLevel)<=level;el.classList.toggle('is-built',shown);el.setAttribute('aria-hidden',String(!shown));});
 document.querySelectorAll('.build-card').forEach(el=>{const n=Number(el.dataset.build),shown=n<=level+1;el.classList.toggle('is-available',shown);el.classList.toggle('is-complete',n<=level);el.inert=!shown;});
 document.querySelectorAll('[data-build-to]').forEach(el=>el.setAttribute('aria-pressed',String(Number(el.dataset.buildTo)===level)));
 $('#next').textContent=['添加 δ₁ →','添加 δ₂ →','加入平方为零 →','加入反交换关系 →','下一页 →'][level];
 $('#prev').disabled=false;$('#clearConcept').hidden=!state.pinned;
 window.spectralState={...state,language:language()};
}
function setBuildStep(level){state.buildStep=Math.max(0,Math.min(4,level));state.pinned=null;updateBuildDOM();applyConcept(null,false);translatePage();}
function revealBuildFor(el){if(!isBuilding())return;const card=el.closest('.build-card');if(card){const level=Number(card.dataset.build);if(level===state.buildStep+1)setBuildStep(level);}}

document.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('.build-card')){e.preventDefault();revealBuildFor(e.target);pinConcept(e.target.dataset.concept);}});
