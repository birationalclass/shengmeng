// Reading references and code provenance are independent of graph roots and Lean status.
// A reference pack is a reading index, not a claim of verbatim textbook formalization.
export const sourcePackDefinitions = [
  {id:'hartshorne',name:['Hartshorne 卡包','Hartshorne'],mark:'H',color:'#6479a9',reference:['I.6 · II.4 · III.11','I.6 · II.4 · III.11'],description:['曲线赋值、Chow 改造与连通纤维。','Curve valuations, Chow modifications and connected fibers.']},
  {id:'ega',name:['EGA 卡包','EGA'],mark:'E',color:'#7b83ac',reference:['EGA III · §3–4','EGA III · §§3–4'],description:['proper 上同调有限性与形式函数；卡片是本项目使用的具体版本。','Proper cohomology finiteness and formal functions; cards state the versions used here.'],url:'https://stacks.math.columbia.edu/tag/02O7'},
  {id:'stacks',name:['Stacks 卡包','Stacks'],mark:'S',color:'#4e9395',reference:['已标注的 Stacks Tags','Recorded Stacks tags'],description:['按源码与图谱已有的参考链接归类。','Grouped by the reference links already recorded in the source atlas.']},
  {id:'mathlib',name:['mathlib 卡包','mathlib'],mark:'M',color:'#5689a9',reference:['mathlib · 已复用接口','mathlib · reused interfaces'],description:['现成 Lean 定理及本项目的接口封装。','Existing Lean theorems and their adapters in this project.']},
  {id:'external',name:['外部代码卡包','External code'],mark:'L',color:'#718eab',reference:['AINTLIB · Laurent Čech','AINTLIB · Laurent Čech'],description:['已审计的外部 Lean 代码复用；查看节点可追溯具体文件。','Audited external Lean code reuse; each node links to its source files.']},
  {id:'literature',name:['其他文献卡包','Other literature'],mark:'R',color:'#a18a9f',reference:['Chen–Moriwaki 等','Chen–Moriwaki and others'],description:['已注明出处的其他文献结果。','Other results with recorded literature references.']},
  {id:'project',name:['本证明卡包','This proof'],mark:'N',color:'#6b8da1',reference:['Negativity · 构造与接合','Negativity · constructions and assembly'],description:['本项目的推导、辅助构造与主定理；未强行指定教材出处。','Project deductions, auxiliary constructions and the main theorem; no textbook attribution is inferred.']}
];

const hartshorne = new Set(['chow','hartshornegraph','curvecenters','curveplaces','connected','codimone','zmtpoint','normalfinite']);
const ega = new Set(['properformalfunctions','relativeformalmap','relativeapprox','relativeinjective','formal42_actual_proper_formal_functions','formal42_actual_rees_h_one_finite','formal42_actual_rees_proper_cech_finite']);
export function sourcePackFor(node){
  if(hartshorne.has(node.id)||/^(Normal)?Hartshorne/.test(node.file||''))return 'hartshorne';
  if(ega.has(node.id))return 'ega';
  const links=(node.upstream||[]).map(r=>r[1]||'');
  if(links.some(u=>u.includes('github.com/CBirkbeck/AINTLIB')||u.includes('github.com/Vilin97/Autoformalization')))return 'external';
  if(links.some(u=>u.includes('github.com/leanprover-community/mathlib4')))return 'mathlib';
  if(links.some(u=>u.includes('stacks.math.columbia.edu')))return 'stacks';
  if(links.some(u=>/^https?:/.test(u)))return 'literature';
  return 'project';
}

export function buildSourcePacks(nodes){
  return sourcePackDefinitions.map(p=>({...p,cards:nodes.filter(n=>sourcePackFor(n)===p.id)})).filter(p=>p.cards.length);
}
