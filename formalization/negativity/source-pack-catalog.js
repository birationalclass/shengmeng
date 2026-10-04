// Reading references and code provenance are independent of graph roots and Lean status.
// A reference pack is a reading index, not a claim of verbatim textbook formalization.
export const sourcePackDefinitions = [
  {id:'hartshorne',name:['Hartshorne 卡包','Hartshorne'],mark:'H',color:'#6479a9',reference:['I.6 · II.4 · III.11','I.6 · II.4 · III.11'],description:['曲线赋值、Chow 改造与连通纤维。','Curve valuations, Chow modifications and connected fibers.']},
  {id:'ega',name:['EGA 卡包','EGA'],mark:'E',color:'#7b83ac',reference:['EGA III · §3–4','EGA III · §§3–4'],description:['proper 上同调有限性与形式函数；卡片是本项目使用的具体版本。','Proper cohomology finiteness and formal functions; cards state the versions used here.'],url:'https://stacks.math.columbia.edu/tag/02O7'},
  {id:'mathlib',name:['mathlib 卡包','mathlib'],mark:'M',color:'#5689a9',reference:['mathlib · 已复用接口','mathlib · reused interfaces'],description:['现成 Lean 定理及本项目的接口封装。','Existing Lean theorems and their adapters in this project.']},
];

const hartshorne = new Set(['chow','hartshornegraph','curvecenters','curveplaces','connected','codimone','zmtpoint','normalfinite']);
const ega = new Set(['properformalfunctions','relativeformalmap','relativeapprox','relativeinjective','formal42_actual_proper_formal_functions','formal42_actual_rees_h_one_finite','formal42_actual_rees_proper_cech_finite']);
export function sourcePackFor(node){
  if(hartshorne.has(node.id)||/^(Normal)?Hartshorne/.test(node.file||''))return 'hartshorne';
  if(ega.has(node.id))return 'ega';
  const links=(node.upstream||[]).map(r=>r[1]||'');
  if(links.some(u=>u.includes('github.com/CBirkbeck/AINTLIB')||u.includes('github.com/Vilin97/Autoformalization')))return 'project';
  if(links.some(u=>u.includes('github.com/leanprover-community/mathlib4')))return 'mathlib';
  return 'project';
}

export function buildSourcePacks(nodes){
  return sourcePackDefinitions.map(p=>({...p,cards:nodes.filter(n=>sourcePackFor(n)===p.id)})).filter(p=>p.cards.length);
}
