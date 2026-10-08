import {createLineCountModel} from './source-line-model.js?v=20261008-nagata-3';
export function installLeanLineCounts({snapshot,nodes}){
 const model=createLineCountModel(snapshot,nodes),byId=new Map(nodes.map(n=>[n.id,n])),cache=new Map();
 const groups=new Map();for(const p of snapshot.paperPacks||[]){groups.set(p.id,p.members.map(id=>byId.get(id)));for(const file of p.files)groups.set('file-'+file.split('/').pop().replace('.lean',''),p.members.map(id=>byId.get(id)).filter(n=>n.file===file));}
 const dependency=n=>{if(!cache.has(n.id))cache.set(n.id,model.pack([n]));return cache.get(n.id);};
 const total=snapshot.files.reduce((s,f)=>s+f.lineCount,0),identity=document.querySelector('.refuge-identity');
 const summary=document.createElement('span');summary.className='lean-source-total';identity.querySelector('h1').after(summary);
 function render(){
  const en=document.documentElement.lang.startsWith('en'),number=n=>n.toLocaleString(en?'en-US':'zh-CN');
  summary.textContent=en?'Lean · '+number(total)+' source lines':'Lean · '+number(total)+' 源码行';summary.dataset.leanTotalLines=total;
  summary.title=en?'All exported project files; independent of the theorem dependency closure.':'导出工程全部文件；与定理实际依赖闭包分开统计。';
  for(const card of document.querySelectorAll('#graph .node[data-node],.proof-worlds .node[data-world-node],.theorem-target-card')){
   const n=byId.get(card.dataset.worldNode||card.dataset.node||card.dataset.targetNode);if(!n)continue;
   const own=model.own(n),all=dependency(n);let badge=card.querySelector(':scope > .node-lean-lines');
   if(!badge){badge=document.createElement('span');badge.className='node-lean-lines';card.append(badge);}
   badge.dataset.leanLines=own.count===null?'':own.count;badge.dataset.leanDependencyLines=all.count;badge.dataset.leanCountMode='declaration-and-closure';
   badge.textContent=(own.count===null?(en?'Generated': '编译器辅助'):(en?'Own '+number(own.count):'本条 '+number(own.count)))+' · Σ '+number(all.count||0);
   badge.title=(en?'Own declaration / complete actual project dependency closure. Overlaps merged; mathlib excluded.':'自身声明 / 完整实际项目依赖闭包；代码区间合并去重，不含 mathlib。')+'\n'+all.ranges.map(r=>r.path+':'+r.startLine+'–'+r.endLine).join('\n');
   badge.setAttribute('aria-label',badge.textContent+'. '+badge.title.split('\n')[0]);
  }
  for(const card of document.querySelectorAll('[data-world-pack]')){
   const members=groups.get(card.dataset.worldPack);if(!members)continue;
   const key=card.dataset.worldPack;if(!cache.has(key))cache.set(key,{own:model.union(members.map(n=>snapshot.sourceRanges[n.decl]).filter(Boolean)),all:model.pack(members)});
   const {own,all}=cache.get(key);let badge=card.querySelector(':scope > .node-lean-lines');if(!badge){badge=document.createElement('span');badge.className='node-lean-lines';card.append(badge);}
   badge.dataset.leanLines=own.count;badge.dataset.leanDependencyLines=all.count;badge.dataset.leanCountMode='members-and-closure';badge.textContent=(en?'Pack ':'本包 ')+number(own.count)+' · Σ '+number(all.count||0);badge.title=en?'Member declaration ranges / full dependency closure; overlaps merged, mathlib excluded.':'包内声明区间 / 完整依赖闭包；合并去重，不含 mathlib。';
  }
 }
 render();window.addEventListener('languagechange',render);document.addEventListener('proofworldrender',render);document.addEventListener('theoremcardchange',render,true);
}
