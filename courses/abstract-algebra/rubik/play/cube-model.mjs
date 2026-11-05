// Exact labelled-facelet model for 2×2×2 through 5×5×5 cubes.
// Products act left to right: compose(a,b)[i] = b[a[i]]. Viewing the cube is not a move.
export const FACES = Object.freeze(['U', 'R', 'F', 'D', 'L', 'B']);
export const NORMALS = Object.freeze({U:[0,1,0], R:[1,0,0], F:[0,0,1], D:[0,-1,0], L:[-1,0,0], B:[0,0,-1]});
export const BASIS = Object.freeze({
  U:[[1,0,0],[0,0,-1]], R:[[0,0,-1],[0,1,0]], F:[[1,0,0],[0,1,0]],
  D:[[1,0,0],[0,0,1]], L:[[0,0,1],[0,1,0]], B:[[-1,0,0],[0,1,0]]
});
export const identity = n => Array.from({length:n}, (_,i) => i);
export const compose = (a,b) => a.map(i => b[i]);
export const inverse = p => {const q=Array(p.length);p.forEach((v,i) => {q[v]=i;});return q;};
export const equal = (a,b) => a.length===b.length && a.every((v,i) => v===b[i]);
function exponent(value) {
  if(typeof value==='bigint')return value;
  if(typeof value==='number' && Number.isSafeInteger(value))return BigInt(value);
  if(typeof value==='string' && /^[-+]?\d+$/.test(value.trim()))return BigInt(value.trim());
  throw new TypeError('次数须为整数；很大的次数请使用十进制字符串。');
}
export function power(p,value) {
  let n=exponent(value),base=p;
  if(n<0n){base=inverse(base);n=-n;}
  let result=identity(p.length);
  while(n){if(n&1n)result=compose(result,base);n>>=1n;if(n)base=compose(base,base);}
  return result;
}
export function cycles(p,includeFixed=false) {
  const seen=new Uint8Array(p.length),out=[];
  for(let i=0;i<p.length;i++){
    if(seen[i])continue;
    const cycle=[];let j=i;
    while(!seen[j]){seen[j]=1;cycle.push(j);j=p[j];}
    if(cycle.length>1||includeFixed)out.push(cycle);
  }
  return out;
}
export const gcd = (a,b) => {a=BigInt(a);b=BigInt(b);while(b){[a,b]=[b,a%b];}return a<0n?-a:a;};
export const lcm = (a,b) => {a=BigInt(a);b=BigInt(b);return a&&b?a/gcd(a,b)*b:0n;};
export const order = p => cycles(p).reduce((a,c) => lcm(a,BigInt(c.length)),1n);
export function analyze(p) {
  const allCycles=cycles(p,true),activeCycles=allCycles.filter(c => c.length>1);
  const counts=new Map();for(const c of activeCycles)counts.set(c.length,(counts.get(c.length)||0)+1);
  const lengths=[...counts.keys()].sort((a,b) => a-b);
  const value=lengths.reduce((a,n) => lcm(a,BigInt(n)),1n);
  return {order:value,cycles:activeCycles,allCycles,lengths,cycleCounts:lengths.map(length => ({length,count:counts.get(length)})),
    moved:activeCycles.reduce((n,c) => n+c.length,0),fixed:allCycles.filter(c => c.length===1).length,degree:p.length};
}
export function rotateQuarter(v,axis,sign) {
  const [x,y,z]=v;
  if(axis===0)return [x,-sign*z,sign*y];
  if(axis===1)return [sign*z,y,-sign*x];
  return [-sign*y,sign*x,z];
}
const key = (p,n) => [...p,...n].join(',');
export function createCube(size) {
  if(!Number.isInteger(size)||size<2||size>5)throw new RangeError('魔方规格须为 2 至 5 阶。');
  const edge=size-1,facelets=FACES.flatMap(face => Array.from({length:size*size},(_,i) => {
    const row=Math.floor(i/size),col=i%size,n=[...NORMALS[face]],[r,u]=BASIS[face];
    return {face,row,col,n,p:n.map((v,j) => v*edge+r[j]*(2*col-edge)+u[j]*(edge-2*row)),label:face+(i+1)};
  }));
  const lookup=new Map(facelets.map((s,i) => [key(s.p,s.n),i])),cache=new Map();
  function normalize(move) {
    const face=String(move?.face||'').toUpperCase(),depth=move?.depth??1,width=move?.width??1,turns=move?.turns??1;
    if(!FACES.includes(face))throw new RangeError('请选择 U、R、F、D、L、B 中的一个方向。');
    if(!Number.isInteger(depth)||!Number.isInteger(width)||depth<1||width<1||depth+width-1>size)throw new RangeError(`${size} 阶魔方的层号须在 1 至 ${size} 之间。`);
    if(![1,-1,2].includes(turns))throw new RangeError('仅支持顺转 90°、逆转 90° 或半转 180°。');
    return {face,depth,width,turns};
  }
  function token(input) {
    const m=normalize(input),prefix=m.width===1?(m.depth===1?'':String(m.depth)):
      m.depth===1?(m.width===2?'':String(m.width)):`${m.depth}-${m.depth+m.width-1}`;
    return prefix+m.face+(m.width>1&&m.depth===1?'w':'')+(m.turns===-1?"'":m.turns===2?'2':'');
  }
  const inverseMoves = moves => [...moves].reverse().map(input => {const m=normalize(input);return {...m,turns:m.turns===2?2:-m.turns};});
  function moveInfo(input) {
    const m=normalize(input),axis=NORMALS[m.face].findIndex(Boolean),sign=NORMALS[m.face][axis];
    return {axis,layers:Array.from({length:m.width},(_,j) => sign*(edge-2*(m.depth-1+j))),angle:-sign*Math.PI/2};
  }
  function movePermutation(input) {
    const m=normalize(input),name=token(m);
    if(cache.has(name))return [...cache.get(name)];
    const {axis,layers}=moveInfo(m),selected=new Set(layers),sign=-NORMALS[m.face][axis];
    const p=facelets.map((s,i) => selected.has(s.p[axis])?lookup.get(key(rotateQuarter(s.p,axis,sign),rotateQuarter(s.n,axis,sign))):i);
    const result=m.turns===1?p:m.turns===-1?inverse(p):compose(p,p);
    if(result.some(i => !Number.isInteger(i)))throw new Error('魔方转动的整数坐标不封闭。');
    cache.set(name,result);return [...result];
  }
  const algorithmPermutation = moves => moves.reduce((p,m) => compose(p,movePermutation(m)),identity(facelets.length));
  function parse(input,options={}) {
    const limit=typeof options==='number'?options:options.limit??2048,maxDepth=typeof options==='number'?32:options.maxDepth??32;
    if(!Number.isSafeInteger(limit)||limit<1||!Number.isSafeInteger(maxDepth)||maxDepth<1)throw new RangeError('无效的算法长度限制。');
    if(typeof input!=='string')throw new TypeError('操作序列须为文本。');
    const s=input.replace(/[’′]/g,"'").trim();let i=0;
    const fail = detail => {throw new Error(`第 ${i+1} 个字符附近无法识别。${detail||"支持 R、2R、Rw、3Rw、逆转 '、半转 2、(…)n、[A,B] 和 [A:B]。"}`);};
    const bound = list => {if(list.length>limit)throw new Error(`展开后最多 ${limit} 步，请缩短操作序列。`);return list;};
    function positive() {const m=s.slice(i).match(/^\d+/);if(!m)return null;i+=m[0].length;const n=Number(m[0]);if(!Number.isSafeInteger(n)||n<1)fail('层号和重复次数须为正整数。');return n;}
    function suffix(part) {
      const count=positive();
      if(count!==null){if(count>limit||part.length*count>limit)bound({length:limit+1});part=Array.from({length:count},() => part).flat();}
      if(s[i]==="'"){i++;part=inverseMoves(part);}
      return part;
    }
    function sequence(stops='',depth=0) {
      if(depth>maxDepth)fail('括号嵌套过深，请简化操作序列。');
      let out=[];
      while(i<s.length){
        if(/\s/.test(s[i])){i++;continue;}
        if(stops.includes(s[i]))break;
        let part;
        if(s[i]==='('){i++;part=sequence(')',depth+1);if(s[i]!==')')fail('缺少右括号。');i++;part=suffix(part);}
        else if(s[i]==='['){
          i++;const a=sequence(',:]',depth+1),sep=s[i++];if(![',',':'].includes(sep))fail('方括号中须使用逗号或冒号。');
          const b=sequence(']',depth+1);if(s[i]!==']'||!a.length||!b.length)fail('交换子或共轭的两段操作不能为空。');i++;
          part=suffix(bound([...a,...b,...inverseMoves(a),...(sep===','?inverseMoves(b):[])]));
        }else{
          const first=positive();let last=null;
          if(first!==null&&s[i]==='-'){i++;last=positive();if(last===null||last<first)fail('层范围须由小到大，例如 2-3R。');}
          const symbol=s[i++];if(!symbol||!FACES.includes(symbol.toUpperCase()))fail();
          const face=symbol.toUpperCase(),lower=symbol!==face;
          let wide=lower;
          if(s[i]==='w'||s[i]==='W'){wide=true;i++;}
          if(last!==null&&wide)fail('层范围不再附加 w，例如 2-3R。');
          let turns=1;
          if(s[i]==='2'){turns=2;i++;if(s[i]==="'")i++;}
          else if(s[i]==="'"){turns=-1;i++;}
          part=[normalize({face,depth:last!==null?first:wide?1:first??1,width:last!==null?last-first+1:wide?first??2:1,turns})];
        }
        out=bound([...out,...part]);
      }
      return out;
    }
    const result=sequence();if(i!==s.length)fail();return result;
  }
  return {size,facelets,identity:() => identity(facelets.length),parse,token,inverseMoves,movePermutation,algorithmPermutation,moveInfo};
}
