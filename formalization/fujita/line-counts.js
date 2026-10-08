import {buildSourcePacks} from './source-pack-catalog.js?v=20261008-fujita-1';
import {createLineCountModel} from './source-line-model.js?v=20261008-fujita-1';
let dispose=()=>{};
export function installLeanLineCounts({snapshot,nodes}){
  dispose();
  if(!document.querySelector('link[data-lean-line-styles]')){
    const css=document.createElement('link');css.rel='stylesheet';css.href=new URL('line-counts.css?v=20261008-fujita-1',import.meta.url).href;css.dataset.leanLineStyles='';document.head.append(css);
  }
  const model=createLineCountModel(snapshot,nodes),byId=new Map(nodes.map(n=>[n.id,n]));
  const packs=new Map(buildSourcePacks(nodes).map(p=>[p.id,model.pack(p.cards)]));
  const files=new Map(snapshot.files.filter(f=>f.path.endsWith('.lean')).map(f=>[f.path,f]));
  const total=files.size>0&&[...files.values()].every(f=>Number.isInteger(f.lineCount))?[...files.values()].reduce((s,f)=>s+f.lineCount,0):null;
  const identity=document.querySelector('.refuge-identity');let summary=identity.querySelector('.lean-source-total');
  if(!summary){summary=document.createElement('span');summary.className='lean-source-total';identity.querySelector('h1').after(summary);}
  summary.dataset.leanTotalLines=total===null?'':String(total);
  function render(){
    const en=document.documentElement.lang.startsWith('en'),number=n=>n.toLocaleString(en?'en-US':'zh-CN');
    const cardRule=en?'This declaration only: compiler-recorded statement and proof range, including comments and blank lines within the range.':'仅本声明：Lean 编译器记录的陈述与证明区间，含区间内注释和空行。';
    const packRule=en?'All member code and actual project-code dependencies; overlapping source ranges counted once. Excludes mathlib sources.':'包内全部声明及实际使用的项目代码依赖；按文件中的代码区间合并去重，不含 mathlib 源码。';
    const totalRule=en?'All exported project Lean files, counted once per file, including the audit script; excludes mathlib.':'公开工程全部 Lean 文件按文件去重，含审计脚本，不含 mathlib。';
    summary.textContent=total===null?(en?'Lean lines unavailable':'Lean 行数未提供'):(en?`Lean · ${number(total)} lines`:`Lean · ${number(total)} 行`);
    summary.title=totalRule;summary.setAttribute('aria-label',summary.textContent+'. '+totalRule);
    for(const card of document.querySelectorAll('#graph .node[data-node],.proof-worlds .node[data-world-node],.proof-worlds .node[data-world-pack],.theorem-target-card')){
      const id=card.dataset.worldNode||card.dataset.node||card.dataset.targetNode;
      const reference=card.dataset.worldPack&&packs.get(card.dataset.worldPack);
      const moduleCover=card.closest('.proof-package')?.dataset.hasCards==='true'&&!card.dataset.worldPack;
      const result=reference||(moduleCover?model.module(id):model.own(byId.get(id)));
      const packed=Boolean(reference||moduleCover),rule=packed?packRule:cardRule;
      let badge=card.querySelector(':scope > .node-lean-lines');
      if(!badge){badge=document.createElement('span');badge.className='node-lean-lines';card.append(badge);}
      badge.dataset.leanLines=result.count===null?'':String(result.count);
      badge.dataset.leanCountMode=packed?'pack':'declaration';
      badge.dataset.leanRanges=JSON.stringify(result.ranges);
      badge.dataset.leanFiles=JSON.stringify([...new Set(result.ranges.map(r=>r.path))]);
      const suffix=result.complete?'':'+';
      const label=packed?'Lean Σ':'Lean';
      badge.textContent=result.count===null?(en?'Lean lines unavailable':'Lean 行数未提供'):(en?`${label} ${number(result.count)}${suffix} lines`:`${label} ${number(result.count)}${suffix} 行`);
      badge.title=result.count===null?(en?'No declaration range is available; this is not a proof-status badge.':'未提供本声明的代码区间；此处不表示证明状态。'):
        result.ranges.map(r=>`${r.path}:${r.startLine}–${r.endLine}`).join('\n')+'\n'+rule+(!result.complete?(en?' Some members have no source declaration yet.':' 部分成员尚无源码声明；显示已知代码的总数。'):'');
      badge.setAttribute('aria-label',badge.textContent+'. '+rule);
    }
  }
  render();window.addEventListener('languagechange',render);document.addEventListener('proofworldrender',render);document.addEventListener('theoremcardchange',render,true);
  dispose=()=>{window.removeEventListener('languagechange',render);document.removeEventListener('proofworldrender',render);document.removeEventListener('theoremcardchange',render,true);};
}
