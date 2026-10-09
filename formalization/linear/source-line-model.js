// Pure range aggregation; shared by badges and verification.
export function createLineCountModel(snapshot,nodes){
  const ranges=snapshot.sourceRanges||{},byId=new Map(nodes.map(n=>[n.id,n]));
  const union=items=>{
    const files=new Map();
    for(const r of items){if(!files.has(r.path))files.set(r.path,[]);files.get(r.path).push([r.startLine,r.endLine]);}
    const merged=[];
    for(const [path,list] of files){
      list.sort((a,b)=>a[0]-b[0]||a[1]-b[1]);let current=null;
      for(const [start,end] of list){
        if(current&&start<=current.endLine+1)current.endLine=Math.max(current.endLine,end);
        else {current={path,startLine:start,endLine:end};merged.push(current);}
      }
    }
    return {ranges:merged,count:merged.reduce((s,r)=>s+r.endLine-r.startLine+1,0)};
  };
  const own=node=>{
    const r=ranges[node?.decl||node?.declaration];
    return r?{...union([r]),complete:true}:{ranges:[],count:null,complete:false};
  };
  const pack=members=>{
    const seen=new Set(),items=[];let complete=true;
    const visit=name=>{if(seen.has(name))return;seen.add(name);const r=ranges[name];if(!r){complete=false;return;}items.push(r);r.dependencies.forEach(visit);};
    for(const n of members){const name=n?.decl||n?.declaration;if(name)visit(name);else complete=false;}
    const result=union(items);return {...result,count:items.length?result.count:null,complete};
  };
  const module=id=>{
    const members=[],seen=new Set();
    const visit=k=>{if(seen.has(k))return;seen.add(k);const n=byId.get(k);if(!n)return;members.push(n);n.deps.forEach(visit);};
    visit(id);return pack(members);
  };
  const memberOwn=members=>{
    const items=[];let complete=true;
    for(const n of members){const r=ranges[n?.decl||n?.declaration];if(r)items.push(r);else complete=false;}
    const result=union(items);return {...result,count:items.length?result.count:null,complete};
  };
  const moduleOwn=id=>{
    const members=[],seen=new Set();
    const visit=k=>{if(seen.has(k))return;seen.add(k);const n=byId.get(k);if(!n)return;members.push(n);n.deps.forEach(visit);};
    visit(id);return memberOwn(members);
  };
  return {own,pack,module,memberOwn,moduleOwn,union};
}
