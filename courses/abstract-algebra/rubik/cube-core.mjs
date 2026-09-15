// Exact geometry and permutations. Products act from left to right: (a b)(i) = b(a(i)).
export const FACES = ['U','R','F','D','L','B'];
export const NORMALS = {U:[0,1,0],R:[1,0,0],F:[0,0,1],D:[0,-1,0],L:[-1,0,0],B:[0,0,-1]};
export const BASIS = {
  U:[[1,0,0],[0,0,-1]], R:[[0,0,-1],[0,1,0]], F:[[1,0,0],[0,1,0]],
  D:[[1,0,0],[0,0,1]], L:[[0,0,1],[0,1,0]], B:[[-1,0,0],[0,1,0]]
};
export const identity = (n=54) => Array.from({length:n},(_,i)=>i);
export const compose = (a,b) => a.map(i=>b[i]);
export const inverse = p => {const q=Array(p.length);p.forEach((v,i)=>q[v]=i);return q;};
export const equal = (a,b) => a.length===b.length && a.every((v,i)=>v===b[i]);
export function power(p,n) {if(n<0)return power(inverse(p),-n);let q=identity(p.length);while(n){if(n%2)q=compose(q,p);p=compose(p,p);n=Math.floor(n/2);}return q;}
const key = (p,n) => [...p,...n].join(',');
export const FACELETS = FACES.flatMap(face=>Array.from({length:9},(_,i)=>{
  const row=Math.floor(i/3),col=i%3,n=NORMALS[face], [r,u]=BASIS[face];
  return {face,row,col,n,p:n.map((v,j)=>v+r[j]*(col-1)+u[j]*(1-row)),label:face+(i+1)};
}));
const index = new Map(FACELETS.map((s,i)=>[key(s.p,s.n),i]));
export function rotateQuarter(v,axis,sign) {
  const [x,y,z]=v;
  if(axis===0)return [x,-sign*z,sign*y];
  if(axis===1)return [sign*z,y,-sign*x];
  return [-sign*y,sign*x,z];
}
export const MOVE_INFO = Object.fromEntries(FACES.map(f=>{const axis=NORMALS[f].findIndex(Boolean),layer=NORMALS[f][axis];return [f,{axis,layer,angle:-layer*Math.PI/2}];}));
export const MOVES = Object.fromEntries(FACES.map(f=>{
  const {axis,layer}=MOVE_INFO[f];
  return [f,FACELETS.map((s,i)=>s.p[axis]===layer?index.get(key(rotateQuarter(s.p,axis,-layer),rotateQuarter(s.n,axis,-layer))):i)];
}));
export const CORNERS = ['URF','UFL','ULB','UBR','DFR','DLF','DBL','DRB'];
export const EDGES = ['UR','UF','UL','UB','DR','DF','DL','DB','FR','FL','BL','BR'];
function slots(names){return names.map(name=>{const fs=[...name],p=[0,1,2].map(j=>fs.reduce((s,f)=>s+NORMALS[f][j],0));return fs.map(f=>index.get(key(p,NORMALS[f])));});}
export const CORNER_SLOTS = slots(CORNERS), EDGE_SLOTS = slots(EDGES);
export const MOBILE = FACELETS.map((_,i)=>i).filter(i=>i%9!==4);
export const mobilePermutation = p => MOBILE.map(i=>MOBILE.indexOf(p[i]));
export function cubies(p) {
  const at=inverse(p), cp=[],co=[],ep=[],eo=[];
  CORNER_SLOTS.forEach(ids=>{
    const colors=ids.map(i=>FACELETS[at[i]].face),o=colors.findIndex(f=>f==='U'||f==='D');
    const piece=CORNERS.findIndex(s=>s[1]===colors[(o+1)%3]&&s[2]===colors[(o+2)%3]);
    if(piece<0||o<0)throw Error('Invalid corner');cp.push(piece);co.push(o);
  });
  EDGE_SLOTS.forEach(ids=>{
    const colors=ids.map(i=>FACELETS[at[i]].face).join('');let piece=EDGES.indexOf(colors),o=0;
    if(piece<0){piece=EDGES.indexOf([...colors].reverse().join(''));o=1;}
    if(piece<0)throw Error('Invalid edge');ep.push(piece);eo.push(o);
  });
  return {cp,co,ep,eo};
}
export function fromCubies({cp,co,ep,eo}){
  const p=identity();
  CORNER_SLOTS.forEach((ids,i)=>ids.forEach((_,j)=>p[CORNER_SLOTS[cp[i]][j]]=ids[(j+co[i])%3]));
  EDGE_SLOTS.forEach((ids,i)=>ids.forEach((_,j)=>p[EDGE_SLOTS[ep[i]][j]]=ids[(j+eo[i])%2]));
  return p;
}
export function cycles(p,includeFixed=false){
  const seen=new Set(),out=[];
  p.forEach((_,i)=>{if(seen.has(i))return;const c=[];let j=i;while(!seen.has(j)){seen.add(j);c.push(j);j=p[j];}if(c.length>1||includeFixed)out.push(c);});
  return out;
}
export const parity = p => cycles(p).reduce((s,c)=>(s+c.length-1)%2,0);
const gcd=(a,b)=>b?gcd(b,a%b):a;
export const order = p => cycles(p).reduce((a,c)=>a/ gcd(a,BigInt(c.length))*BigInt(c.length),1n);
export function invariants(p){const c=cubies(p),twist=c.co.reduce((a,b)=>a+b,0)%3,flip=c.eo.reduce((a,b)=>a+b,0)%2,cornerParity=parity(c.cp),edgeParity=parity(c.ep);return {...c,twist,flip,cornerParity,edgeParity,legal:!twist&&!flip&&cornerParity===edgeParity};}
export const token = m => m.face+(m.turns===-1?"'":m.turns===2?'2':'');
export const invertMoves = ms => [...ms].reverse().map(m=>({face:m.face,turns:m.turns===2?2:-m.turns}));
export const movePermutation = m => power(MOVES[m.face],m.turns);
export const algorithmPermutation = ms => ms.reduce((p,m)=>compose(p,movePermutation(m)),identity());
export function parseAlgorithm(input,limit=400){
  const s=input.replace(/[’′]/g,"'").trim();let i=0;
  const fail=()=>{throw Error(`第 ${i+1} 个字符附近无法识别。请使用 R U F D L B、逆转 '、半转 2、(…)n、[A,B] 或 [A:B]。`);};
  const bound=a=>{if(a.length>limit)throw Error(`一次最多 ${limit} 步，请分段演示。`);return a;};
  function sequence(stops=''){
    let out=[];
    while(i<s.length){if(/\s/.test(s[i])){i++;continue;}if(stops.includes(s[i]))break;
      let part;
      if(s[i]==='('){i++;part=sequence(')');if(s[i++]!==')')fail();const m=s.slice(i).match(/^\d+/);if(m){i+=m[0].length;const n=Number(m[0]);if(n<1||n>limit)fail();part=bound(Array.from({length:n},()=>part).flat());}}
      else if(s[i]==='['){i++;const a=sequence(',:]'),sep=s[i++];if(![',',':'].includes(sep))fail();const b=sequence(']');if(s[i++]!==']'||!a.length||!b.length)fail();part=[...a,...b,...invertMoves(a),...(sep===','?invertMoves(b):[])];}
      else {const face=s[i++].toUpperCase();if(!FACES.includes(face))fail();let turns=1;if(s[i]==='2'){turns=2;i++;if(s[i]==="'")i++;}else if(s[i]==="'"){turns=-1;i++;}part=[{face,turns}];}
      out=bound([...out,...part]);
    }return out;
  }
  const out=sequence();if(i!==s.length)fail();return out;
}
export function scramble(length=20,random=Math.random){const out=[];while(out.length<length){const face=FACES[Math.floor(random()*6)];if(out.at(-1)?.face===face)continue;out.push({face,turns:[1,-1,2][Math.floor(random()*3)]});}return out;}
export function impossible(kind){const c=cubies(identity());if(kind==='flip')c.eo[0]=1;else if(kind==='twist')c.co[0]=1;else if(kind==='parity')[c.ep[0],c.ep[1]]=[c.ep[1],c.ep[0]];else throw Error('Unknown example');return fromCubies(c);}
