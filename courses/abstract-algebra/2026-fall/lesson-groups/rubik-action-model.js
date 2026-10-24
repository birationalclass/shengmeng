/* Exact quarter-turn permutations. Intermediate rendering poses are not states. */
(function(root,factory){const api=factory();if(typeof module==='object'&&module.exports)module.exports=api;else root.RubikActionModel=api;})(typeof window==='object'?window:globalThis,function(){
 'use strict';
 const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
 const cross=(a,b)=>[a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]];
 const faces=[['U',[0,1,0],[1,0,0],[0,0,1],'#f5ecd8'],['R',[1,0,0],[0,0,-1],[0,-1,0],'#de4d52'],['F',[0,0,1],[1,0,0],[0,-1,0],'#39c188'],['D',[0,-1,0],[1,0,0],[0,0,-1],'#f1d24b'],['L',[-1,0,0],[0,0,1],[0,-1,0],'#ed9541'],['B',[0,0,-1],[-1,0,0],[0,-1,0],'#508cde']];
 const slots=[];
 for(const [face,n,u,v,color]of faces)for(let row=-1;row<=1;row++)for(let col=-1;col<=1;col++)slots.push({face,n,u,v,color,p:n.map((a,i)=>a+u[i]*col+v[i]*row)});
 const key=(p,n)=>p.concat(n).join(','),lookup=new Map(slots.map((s,i)=>[key(s.p,s.n),i]));
 const identity=()=>Array.from({length:54},(_,i)=>i);
 const compose=(a,b)=>b.map(i=>a[i]); // a after b
 function rotate(v,axis,angle){const a=[0,0,0];a[axis]=1;const c=Math.cos(angle),s=Math.sin(angle),k=dot(a,v),w=cross(a,v);return v.map((x,i)=>x*c+w[i]*s+a[i]*k*(1-c));}
 const turns={};
 for(const [face,n]of faces){const axis=n.findIndex(x=>x!==0),layer=n[axis],q=-layer;
  const permutation=slots.map(s=>s.p[axis]===layer?lookup.get(key(rotate(s.p,axis,q*Math.PI/2).map(Math.round),rotate(s.n,axis,q*Math.PI/2).map(Math.round))):lookup.get(key(s.p,s.n)));
  turns[face]={face,axis,layer,q,permutation};
 }
 function parse(text){const clean=String(text).trim().replace(/[’′]/g,"'");if(!clean)return[];const tokens=clean.split(/\s+/);if(tokens.length>40||tokens.some(t=>!/^([RLUDFB])(['2]?)$/.test(t)))throw Error('Use R L U D F B, optionally followed by an apostrophe or 2; separate moves with spaces.');return tokens;}
 function inverse(p){const out=identity();p.forEach((j,i)=>out[j]=i);return out;}
 function power(p,n){if(n<0)return power(inverse(p),-n);let out=identity(),a=p;while(n){if(n%2)out=compose(a,out);a=compose(a,a);n=Math.floor(n/2);}return out;}
 function tokenInfo(token){const face=token[0],amount=token.endsWith('2')?2:token.endsWith("'")?-1:1;const turn=turns[face];return{...turn,token,amount,angle:turn.q*amount*Math.PI/2,permutation:power(turn.permutation,amount)};}
 function word(text){return parse(text).reduce((p,t)=>compose(tokenInfo(t).permutation,p),identity());}
 function apply(p,state){const out=identity();p.forEach((j,i)=>out[j]=state[i]);return out;}
 function cycles(p){const seen=new Set(),out=[];for(let i=0;i<54;i++){if(seen.has(i))continue;const c=[];let j=i;do{c.push(j);seen.add(j);j=p[j];}while(j!==i);out.push(c);}return out;}
 const gcd=(a,b)=>b?gcd(b,a%b):a;
 const order=p=>cycles(p).reduce((a,c)=>a/gcd(a,c.length)*c.length,1);
 const same=(a,b)=>a.every((x,i)=>x===b[i]);
 const presets=['U',"R U R' U'",'R U',"R U2 F' L"];
 function at(base,p,n){return apply(power(p,n),base);}
 return{slots,faces,turns,identity,compose,rotate,parse,tokenInfo,inverse,power,word,apply,cycles,order,same,at,presets};
});
