import {auditedStatements} from './audited-statement-data.js?v=20261004-explain-47';
const escape=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
export const shortType=t=>t.replace(/\b(?:AlgebraicGeometry|CategoryTheory(?:\.Limits)?|TopologicalSpace|Negativity|_root_)\./g,'').replace(/\s+/g,' ').trim();
const predicates={
 IsIntegral:['为整概形','is integral'],IsAffine:['为仿射概形','is affine'],IsAffineOpen:['为仿射开集','is an affine open'],IsLocallyNoetherian:['局部 Noetherian','is locally Noetherian'],IsNoetherian:['为 Noetherian 概形','is Noetherian'],IsProper:['为 proper 态射','is proper'],IsFinite:['为有限态射','is finite'],BirationalMorphism:['为双有理态射','is birational'],LocallyOfFiniteType:['局部有限型','is locally of finite type'],IsClosedImmersion:['为闭嵌入','is a closed immersion'],IsOpenImmersion:['为开嵌入','is an open immersion'],IsSeparated:['为分离态射','is separated'],IsDominant:['为支配态射','is dominant'],QuasiCompact:['拟紧','is quasi-compact'],LocallyQuasiFinite:['局部拟有限','is locally quasi-finite'],IsAlgClosed:['为代数闭域','is algebraically closed'],PerfectField:['为 perfect 域','is a perfect field'],Field:['为域','is a field'],CommRing:['为交换环','is a commutative ring'],Ring:['为环','is a ring'],Semiring:['为半环','is a semiring'],IsDomain:['为整环','is a domain'],IsNoetherianRing:['为 Noetherian 环','is Noetherian'],IsIntegrallyClosed:['整闭','is integrally closed'],IsDedekindDomain:['为 Dedekind 整环','is a Dedekind domain'],IsDiscreteValuationRing:['为 DVR','is a DVR'],IsLocalRing:['为局部环','is a local ring'],CompactSpace:['拟紧','is quasi-compact'],ConnectedSpace:['连通','is connected'],Fintype:['为有限指标集','is a finite index set'],Finite:['为有限集','is finite'],IsClosed:['为闭集','is closed'],IsClopen:['为开闭集','is clopen'],FunctionInjective:['为单射','is injective'],FunctionSurjective:['为满射','is surjective'],AddCommGroup:['为交换群','is an abelian group'],LinearOrder:['为线序','is linearly ordered'],DecidableEq:['具有可判定相等关系','has decidable equality']
};
export function readableCondition(raw,en){
 const t=shortType(raw),plain=t.replace(/^Function\.(Injective|Surjective)/,(_,s)=>'Function'+s);
 const m=plain.match(/^([A-Za-z]+) (.+)$/);if(m&&predicates[m[1]])return `${m[2]} ${predicates[m[1]][en?1:0]}`;
 if(/^∀.*IsIntegrallyClosed.*presheaf\.stalk/.test(t)){const x=t.match(/([A-Za-zΑ-ω]+)\.presheaf\.stalk/)?.[1];if(x)return en?`${x} is normal`:`${x} 正规`;}
 if(/^∀.*IsAffineOpen/.test(t)&&t.includes('⊓'))return en?(t.split('⊓').length>2?'All indicated triple intersections are affine':'All indicated pairwise intersections are affine'):(t.split('⊓').length>2?'各指定三重交集仿射':'各指定二重交集仿射');
 if(t.startsWith('ActualReesCoordinateRestrictionCompatibility '))return en?'The Rees coordinates commute with restriction maps':'Rees 坐标与限制映射相容';
 if(t.startsWith('Effective '))return en?`${t.slice(10)} ≥ 0 (coefficientwise)`:`${t.slice(10)} ≥ 0（逐系数）`;
 if(t.startsWith('¬Effective '))return en?`${t.slice(11)} is not effective`:`${t.slice(11)} 非有效`;
 if(t.startsWith('Module.Finite '))return en?'The displayed module is finitely generated over its scalar ring':'指定模在其标量环上有限生成';
 if(t.startsWith('Algebra.FiniteType '))return en?'The indicated algebra is of finite type':'指定代数为有限型';
 if(t.startsWith('Algebra.IsSeparable '))return en?'The indicated field extension is separable':'指定域扩张可分';
 return t;
}
export function mathText(raw){
 let html=escape(String(raw??''));
 const atom=t=>`<${/^[0-9]+$/.test(t)?'mn':'mi'}>${t==='*'?'∗':t}</${/^[0-9]+$/.test(t)?'mn':'mi'}>`;
 html=html.replace(/(^|[^A-Za-z0-9_])([A-Zfghπδ×𝒪])\s*([_^])\s*(?:\{([^}]+)\}|([*0-9ijknmSXYC-]+))/g,(_,prefix,base,op,a,b)=>`${prefix}<math xmlns="http://www.w3.org/1998/Math/MathML"><${op==='^'?'msup':'msub'}>${atom(base)}<mrow>${atom(a||b)}</mrow></${op==='^'?'msup':'msub'}></math>`);
 html=html.replace(/f∗D/g,'<math xmlns="http://www.w3.org/1998/Math/MathML" aria-label="f_*D"><msub><mi>f</mi><mo>∗</mo></msub><mi>D</mi></math>');
 return html;
}
export function compiledStatement(n,en){
 const record=auditedStatements[n.id];if(!record||record.declaration!==n.decl)throw new Error('Missing audited statement: '+n.id);
 const objects=record.parameters.filter(p=>!p.proposition&&!p.instance);
 const assumptions=record.parameters.filter(p=>p.proposition||p.instance);
 const objectText=objects.map(p=>{let type=shortType(p.type);if(/^Type(?: |$)/.test(type)){const ring=record.parameters.find(q=>new RegExp(`^(Field|CommRing|Ring|Semiring) ${p.name}$`).test(shortType(q.type)));type=ring?(en?{Field:'field',CommRing:'commutative ring',Ring:'ring',Semiring:'semiring'}:{Field:'域',CommRing:'交换环',Ring:'环',Semiring:'半环'})[shortType(ring.type).split(' ')[0]]:(en?'type':'集合');}type=type.replace(/(\S+) → ↑?([A-Za-z]+)\.affineOpens/g,(_,i,x)=>en?`family of affine opens of ${x}, indexed by ${i}`:`${x} 的仿射开集族（指标 ${i}）`).replace(/(\S+) → ([A-Za-z]+)\.Opens/g,(_,i,x)=>en?`family of opens of ${x}, indexed by ${i}`:`${x} 的开集族（指标 ${i}）`);type=type.replace(/Scheme\.\{[^}]+\}/g,'Scheme').replace(/\bScheme\b/g,en?'scheme':'概形');return `${p.name.replace(/✝/g,'′')} : ${type}`;}).join('; ');
 const conditions=assumptions.map((p,i)=>({name:p.name.startsWith('inst.')?null:p.name,label:readableCondition(p.type,en),exact:p.type}));
 const important=conditions.filter(c=>!/^.*(?:commutative ring|is a field|index set|交换环|为域|指标集|decidable equality|可判定相等)/.test(c.label));
 const compactLet=(important.length?important:conditions).slice(0,2).map(c=>c.label).join('; ')||objectText|| (en?'Use the displayed mathematical data.':'取所列数学对象。');
 const statement=n.statement||n.title;
 return {let:objectText?`${en?'Let':'设'} ${mathText(objectText)}.`:(en?'Use the following mathematical data.':'取以下数学数据。'),conditions,then:mathText(statement),compactLet,compactThen:statement,record};
}
export function exactStatementDetails(n,en){const r=auditedStatements[n.id];return `<details class="statement-exact"><summary>${en?'Complete conditions and conclusion · compiled Lean type':'完整条件与结论 · 已编译 Lean 类型'}</summary><pre><code>${escape(r.type)}</code></pre></details>`;}
