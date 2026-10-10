import {buildSourcePacks} from './source-pack-catalog.js?v=20261011-linear-88';
import {createLineCountModel} from './source-line-model.js?v=20261011-linear-88';
let dispose=()=>{};
export function installLeanLineCounts({snapshot,nodes}){
  dispose();
  if(!document.querySelector('link[data-lean-line-styles]')){
    const css=document.createElement('link');css.rel='stylesheet';css.href=new URL('line-counts.css?v=20261011-linear-88',import.meta.url).href;css.dataset.leanLineStyles='';document.head.append(css);
  }
  const model=createLineCountModel(snapshot,nodes),byId=new Map(nodes.map(n=>[n.id,n]));
  const packs=new Map(buildSourcePacks(nodes).map(p=>[p.id,{own:model.memberOwn(p.cards),all:model.pack(p.cards)}]));
  const files=new Map(snapshot.files.filter(f=>f.path.endsWith('.lean')).map(f=>[f.path,f]));
  const total=[...files.values()].every(f=>Number.isInteger(f.lineCount))?[...files.values()].reduce((s,f)=>s+f.lineCount,0):null;
  const identity=document.querySelector('.refuge-identity');let summary=identity.querySelector('.lean-source-total');
  if(!summary){summary=document.createElement('span');summary.className='lean-source-total';identity.querySelector('h1').after(summary);}
  summary.dataset.leanTotalLines=total===null?'':String(total);
  function render(){
    const en=document.documentElement.lang.startsWith('en'),number=n=>n.toLocaleString(en?'en-US':'zh-CN');
    const cardRule=en?'Own declaration / all project code needed by this declaration. The denominator includes the declaration and its compiler-recorded transitive dependencies. Overlapping ranges counted once; excludes mathlib.':'本声明自身 / 本声明所需全部项目 Lean 代码。后者包含自身及编译器记录的全部传递依赖，重叠代码区间去重，不含 mathlib。';
    const packRule=en?'Member declarations / all member code and its actual project-code dependencies. Overlapping ranges counted once; excludes mathlib.':'包内成员自身代码 / 成员及其实际项目代码依赖。按文件合并重叠区间去重，不含 mathlib。';
    const totalRule=en?'All exported project Lean files, counted once per file, including the audit script; excludes mathlib.':'公开工程全部 Lean 文件按文件去重，含审计脚本，不含 mathlib。';
    summary.textContent=total===null?(en?'Lean lines unavailable':'Lean 行数未提供'):(en?`Lean · ${number(total)} lines`:`Lean · ${number(total)} 行`);
    summary.title=totalRule;summary.setAttribute('aria-label',summary.textContent+'. '+totalRule);
    for(const card of document.querySelectorAll('#graph .node[data-node],.proof-worlds .node[data-world-node],.proof-worlds .node[data-world-pack],.theorem-target-card')){
      const id=card.dataset.worldNode||card.dataset.node||card.dataset.targetNode;
      const reference=card.dataset.worldPack&&packs.get(card.dataset.worldPack);
      const moduleCover=card.closest('.proof-package')?.dataset.hasCards==='true'&&!card.dataset.worldPack;
      const result=reference?.own||(moduleCover?model.moduleOwn(id):model.own(byId.get(id)));
      const all=reference?.all||(moduleCover?model.module(id):model.pack([byId.get(id)]));
      const packed=Boolean(reference||moduleCover),rule=packed?packRule:cardRule;
      let badge=card.querySelector(':scope > .node-lean-lines');
      if(!badge){badge=document.createElement('span');badge.className='node-lean-lines';card.append(badge);}
      badge.dataset.leanLines=result.count===null?'':String(result.count);
      badge.dataset.leanOwnLines=result.count===null?'':String(result.count);
      badge.dataset.leanAllLines=all.count===null?'':String(all.count);
      badge.dataset.leanCountMode=packed?'pack':'declaration';
      badge.dataset.leanRanges=JSON.stringify(result.ranges);
      badge.dataset.leanAllRanges=JSON.stringify(all.ranges);
      badge.dataset.leanFiles=JSON.stringify([...new Set(result.ranges.map(r=>r.path))]);
      const amount=r=>r.count===null?'?':number(r.count)+(r.complete?'':'+');
      badge.textContent=en?`Lean ${amount(result)} / ${amount(all)} lines`:`Lean ${amount(result)} / ${amount(all)} 行`;
      badge.title=rule+'\n'+(en?'Own ranges:':'自身范围：')+'\n'+
        result.ranges.map(r=>`${r.path}:${r.startLine}–${r.endLine}`).join('\n')+'\n'+
        (en?'All needed ranges:':'全部所需范围：')+'\n'+
        all.ranges.map(r=>`${r.path}:${r.startLine}–${r.endLine}`).join('\n')+
        (!result.complete||!all.complete?(en?' ? means no range; + marks only known code. This is not a proof-status badge.':' ? 表示无源码范围；+ 表示仅统计已知代码。此处不表示证明状态。'):'');
      badge.setAttribute('aria-label',badge.textContent+'. '+rule);
    }
  }
  render();window.addEventListener('languagechange',render);document.addEventListener('proofworldrender',render);document.addEventListener('theoremcardchange',render,true);
  dispose=()=>{window.removeEventListener('languagechange',render);document.removeEventListener('proofworldrender',render);document.removeEventListener('theoremcardchange',render,true);};
}
