const encoder=new TextEncoder();
const crcTable=Uint32Array.from({length:256},(_,n)=>{for(let k=0;k<8;k++)n=n&1?0xedb88320^(n>>>1):n>>>1;return n>>>0;});
function crc32(bytes){let n=0xffffffff;for(const b of bytes)n=crcTable[(n^b)&255]^(n>>>8);return(n^0xffffffff)>>>0;}
export function zipStore(files){
 const blocks=[],directory=[];let offset=0,centralSize=0;
 for(const [name,content] of Object.entries(files)){
  const filename=encoder.encode(name),bytes=typeof content==='string'?encoder.encode(content):content,crc=crc32(bytes);
  const local=new Uint8Array(30+filename.length),v=new DataView(local.buffer);
  v.setUint32(0,0x04034b50,true);v.setUint16(4,20,true);v.setUint16(6,0x800,true);v.setUint32(14,crc,true);v.setUint32(18,bytes.length,true);v.setUint32(22,bytes.length,true);v.setUint16(26,filename.length,true);local.set(filename,30);
  blocks.push(local,bytes);
  const central=new Uint8Array(46+filename.length),c=new DataView(central.buffer);
  c.setUint32(0,0x02014b50,true);c.setUint16(4,20,true);c.setUint16(6,20,true);c.setUint16(8,0x800,true);c.setUint32(16,crc,true);c.setUint32(20,bytes.length,true);c.setUint32(24,bytes.length,true);c.setUint16(28,filename.length,true);c.setUint32(42,offset,true);central.set(filename,46);directory.push(central);centralSize+=central.length;offset+=local.length+bytes.length;
 }
 const end=new Uint8Array(22),e=new DataView(end.buffer),count=directory.length;e.setUint32(0,0x06054b50,true);e.setUint16(8,count,true);e.setUint16(10,count,true);e.setUint32(12,centralSize,true);e.setUint32(16,offset,true);
 return new Blob([...blocks,...directory,end],{type:'application/zip'});
}
export function modelFiles(items,material,metadata){
 const obj=['# Local volumetric calligraphy','mtllib surface.mtl','usemtl Surface'];let offset=1;
 for(const item of items.filter(i=>i.mesh.visible)){
  const g=item.g,p=g.attributes.position,n=g.attributes.normal,uv=g.attributes.uv,ix=g.index.array,move=item.mesh.position;
  obj.push('o gesture_'+String(item.i+1).padStart(2,'0'));
  for(let k=0;k<p.count;k++)obj.push('v '+[p.getX(k)+move.x,p.getY(k)+move.y,p.getZ(k)+move.z].map(v=>v.toFixed(7)).join(' '));
  for(let k=0;k<n.count;k++)obj.push('vn '+[n.getX(k),n.getY(k),n.getZ(k)].map(v=>v.toFixed(7)).join(' '));
  for(let k=0;k<uv.count;k++)obj.push('vt '+uv.getX(k).toFixed(6)+' '+uv.getY(k).toFixed(6));
  for(let k=0;k<ix.length;k+=3)obj.push('f '+[ix[k],ix[k+1],ix[k+2]].map(i=>{const v=i+offset;return `${v}/${v}/${v}`;}).join(' '));offset+=p.count;
 }
 const c=material.color;
 return {'calligraphy.obj':obj.join('\n')+'\n','surface.mtl':`newmtl Surface\nKd ${c.r} ${c.g} ${c.b}\nKs 1 1 1\nNs ${2/Math.max(.001,material.roughness**2)-2}\nPm ${material.metalness}\nPr ${material.roughness}\nillum 2\n`,'settings.json':JSON.stringify(metadata,null,2),'README.txt':'本地重建立体书法。OBJ 导出当前进度、可见笔画、分解距离、饱满度、空间起伏和实体细槽。模型以字心为原点，Y 朝上。MTL 含基础色、金属度和粗糙度；清漆、各向异性、布光、镜头等完整参数见 settings.json，导入其他软件需重新设置。各笔画保持独立封闭网格，未做布尔并集；不保证无自交。未取得薄煙原作者工程。天字中线数据沿用 Hanzi Writer Data，许可见项目原目录 ARPHICPL.TXT。\n'};
}
