export function createProofPackages(nodes,complete){
 const byId=new Map(nodes.map(n=>[n.id,n])),cache=new Map(),owner=new Map(),packs=new Map();
 const closure=id=>{if(cache.has(id))return cache.get(id);const found=new Set(),todo=[id];while(todo.length){const k=todo.pop();if(found.has(k)||!byId.has(k))continue;found.add(k);todo.push(...byId.get(k).deps);}cache.set(id,found);return found;};
 const references=complete.paperPacks.map(p=>{
  const allCards=p.members.map(id=>byId.get(id));
  const subpacks=p.files.map(file=>{
   const basename=file.split('/').pop(),all=allCards.filter(n=>n.file===file);
   const f={id:'file-'+basename.replace('.lean',''),kind:'file',file,name:[basename,basename],mark:'Lean',reference:[p.titles[0],p.titles[1]],allCards:all,cards:all.filter(n=>!n.generated),subpacks:[]};
   packs.set(f.id,f);for(const n of all)owner.set(n.id,'pack:'+f.id);return f;
  });
  const item={id:p.id,kind:'paper',section:p.section,name:p.titles,mark:'§'+p.section,reference:['论文 §'+p.section+' 的实现模块','Implementation modules for paper §'+p.section],allCards,cards:allCards.filter(n=>!n.generated),subpacks,mainMembers:p.mainMembers};packs.set(item.id,item);return item;
 });
 return {byId,roots:[],references,owner,closure,members:id=>id?.startsWith('pack:')?packs.get(id.slice(5))?.cards||[]:[...closure(id)].map(k=>byId.get(k)),children:id=>byId.get(id)?.deps||[],isPackage:id=>(byId.get(id)?.deps.length||0)>=2,packFor:id=>packs.get(id)};
}
