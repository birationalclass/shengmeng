// Main-screen organization only; compiler dependencies remain a separate graph.
export function paginateOverview(items,page,capacity=9){
  const pins=items.filter(item=>item.n?.paperCard),others=items.filter(item=>!item.n?.paperCard);
  const pinned=pins.length>0&&pins.length<capacity;
  const pageable=pinned?others:items,pageSize=pinned?capacity-pins.length:capacity;
  const pages=Math.max(1,Math.ceil(pageable.length/pageSize)),current=Math.max(0,Math.min(page,pages-1));
  const start=current*pageSize,end=Math.min(pageable.length,start+pageSize);
  return {shown:[...(pinned?pins:[]),...pageable.slice(start,end)],page:current,pages,
    pinned:pinned?pins.length:0,start:pageable.length?start+1:0,end,total:pageable.length};
}
export function visibleOverviewEdges(model,visibleIds,target='lemma'){
  const visible=new Set(visibleIds),edges=[];
  for(const id of visible){
    for(const dep of model.children(id))if(dep!==id&&visible.has(dep))edges.push({source:dep,target:id,kind:'support'});
  }
  for(const dep of model.children(target))if(visible.has(dep))edges.push({source:dep,target,kind:'route'});
  return edges;
}
