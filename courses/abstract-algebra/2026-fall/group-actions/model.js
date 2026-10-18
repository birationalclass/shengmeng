/* Pure models. Rendering never invents a legal move or a computed coefficient. */
const ActionMath=(()=>{
 const dot=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0), norm=a=>Math.hypot(...a),add=(a,b)=>a.map((x,i)=>x+b[i]),scale=(a,t)=>a.map(x=>x*t),unit=a=>scale(a,1/norm(a));
 const identity=Array.from({length:16},(_,i)=>(i+1)%16);
 function sign(a){let n=0;const p=a.map(x=>x===0?16:x);for(let i=0;i<p.length;i++)for(let j=i+1;j<p.length;j++)if(p[i]>p[j])n++;return n%2?-1:1}
 function invariant(a){const z=a.indexOf(0);return sign(a)*((-1)**(Math.floor(z/4)+z%4+2))}
 function neighbors(a){const z=a.indexOf(0);return [z-4,z+4,z-1,z+1].filter(p=>p>=0&&p<16&&Math.abs(Math.floor(z/4)-Math.floor(p/4))+Math.abs(z%4-p%4)===1)}
 function slide(a,p){if(!neighbors(a).includes(p))throw Error('Illegal slide');const b=a.slice(),z=b.indexOf(0);[b[z],b[p]]=[b[p],b[z]];return b}
 function edgeAction(a,u,v){if(Math.abs(Math.floor(u/4)-Math.floor(v/4))+Math.abs(u%4-v%4)!==1)throw Error('Not an edge');return a[u]===0?slide(a,v):a[v]===0?slide(a,u):a.slice()}
 function walk(seed=1,count=60,start=identity){let a=start.slice(),old=-1;const states=[a],moves=[];for(let i=0;i<count;i++){seed=(1664525*seed+1013904223)>>>0;let ps=neighbors(a).filter(p=>p!==old);const p=ps[seed%ps.length];old=a.indexOf(0);moves.push(p);a=slide(a,p);states.push(a)}return {states,moves}}
 function rotate(v,axis,t){const a=axis==='x'?0:axis==='y'?1:2,b=(a+1)%3,c=(a+2)%3,w=v.slice();w[b]=Math.cos(t)*v[b]-Math.sin(t)*v[c];w[c]=Math.sin(t)*v[b]+Math.cos(t)*v[c];return w}
 const det=([a,b,c])=>a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0]);
 const qconj=q=>[q[0],-q[1],-q[2],-q[3]];
 const qmul=(p,q)=>[p[0]*q[0]-p[1]*q[1]-p[2]*q[2]-p[3]*q[3],p[0]*q[1]+p[1]*q[0]+p[2]*q[3]-p[3]*q[2],p[0]*q[2]-p[1]*q[3]+p[2]*q[0]+p[3]*q[1],p[0]*q[3]+p[1]*q[2]-p[2]*q[1]+p[3]*q[0]];
 function omul(p,q){const a=p.slice(0,4),b=p.slice(4),c=q.slice(0,4),d=q.slice(4);return add(qmul(a,c),scale(qmul(qconj(d),b),-1)).concat(add(qmul(d,a),qmul(b,qconj(c))))}
 const basis=i=>Array.from({length:8},(_,j)=>+(i===j));
 const rotatePair=(f,g,n,x)=>[Math.cos(n*x)*f-Math.sin(n*x)*g,Math.sin(n*x)*f+Math.cos(n*x)*g];
 const signal=x=>.3+Math.cos(x)+.65*Math.sin(2*x)+.35*Math.cos(3*x)+.25*Math.sin(5*x);
 function coefficients(n,N=4096){let a=0,b=0;for(let j=0;j<N;j++){const x=-Math.PI+(j+.5)*2*Math.PI/N,[u,v]=rotatePair(signal(x),0,n,x);a+=u*2/N;b+=v*2/N}return [a,b]}
 function partial(x,N){let y=.3;for(const [n,a,b]of [[1,1,0],[2,0,.65],[3,.35,0],[5,0,.25]])if(n<=N)y+=a*Math.cos(n*x)+b*Math.sin(n*x);return y}
 function noFixedMap(x){return scale(rotate(x,'z',.7),-1)}
 const homotopy=(x,t)=>unit(add(scale(noFixedMap(x),1-t),scale(x,-t)));
 function cube(){const pieces=[];for(let x=-1;x<=1;x++)for(let y=-1;y<=1;y++)for(let z=-1;z<=1;z++){if(!x&&!y&&!z)continue;const stickers=[];for(const [axis,sgn,color]of [[0,1,'#e8313c'],[0,-1,'#ff8a1f'],[1,1,'#f5f5f5'],[1,-1,'#ffd500'],[2,1,'#18b35a'],[2,-1,'#1f6fe0']])if([x,y,z][axis]===sgn){const n=[0,0,0];n[axis]=sgn;stickers.push({normal:n,color})}pieces.push({pos:[x,y,z],stickers,frame:[[1,0,0],[0,1,0],[0,0,1]]})}return pieces}
 function cubeTurn(pieces,axis,layer,angle){const k='xyz'.indexOf(axis);return pieces.map(p=>Math.abs(p.pos[k]-layer)<.01?{...p,pos:rotate(p.pos,axis,angle),frame:p.frame.map(v=>rotate(v,axis,angle)),stickers:p.stickers.map(s=>({...s,normal:rotate(s.normal,axis,angle)}))}:p)}
 function cubeSequence(t,start=cube()){let state=start;const moves=[['y',1,1],['x',1,1],['z',1,-1],['y',1,-1],['x',1,-1],['z',1,1]],whole=Math.floor(t),phase=t-whole;for(let j=0;j<whole;j++){const [a,l,s]=moves[j%moves.length];state=cubeTurn(state,a,l,s*Math.PI/2)}const [a,l,s]=moves[whole%moves.length];return cubeTurn(state,a,l,s*Math.PI/2*(phase*phase*(3-2*phase)))}
 function audit(){let a=identity.slice(),moves=0;for(let s=1;s<=40;s++){const w=walk(s,80);for(let j=1;j<w.states.length;j++){if(invariant(w.states[j])!==1)throw Error('Puzzle invariant');if(sign(w.states[j])!==-sign(w.states[j-1]))throw Error('Permutation sign');moves++}}
 const swapped=identity.slice();[swapped[13],swapped[14]]=[swapped[14],swapped[13]];
 for(const [u,v]of [[0,1],[5,6],[11,15]]){const b=edgeAction(edgeAction(a,u,v),u,v);if(b.some((x,i)=>x!==a[i]))throw Error('Edge action is not involutive')}
 let err=0;for(let i=1;i<=30;i++){const p=unit([Math.sin(i),Math.cos(2*i),.3,.4]),q=unit([.1,Math.cos(i),Math.sin(i),.2]),r=unit([.2,.3,Math.sin(3*i),Math.cos(i)]);err=Math.max(err,norm(add(qmul(qmul(p,q),r),scale(qmul(p,qmul(q,r)),-1))),Math.abs(norm(qmul(p,q))-1));}
 const left=omul(omul(basis(1),basis(2)),basis(4)),right=omul(basis(1),omul(basis(2),basis(4)));
 if(left[7]!==1||right[7]!==-1||invariant(swapped)!==-1||err>1e-12)throw Error('Algebra model failure');
 let actionErr=0,denomMin=2;for(let j=0;j<90;j++){const x=j*.17,[u,v]=rotatePair(.4,-.3,3,x),[a,b]=rotatePair(u,v,-5,x),[c,d]=rotatePair(.4,-.3,-2,x);actionErr=Math.max(actionErr,Math.hypot(a-c,b-d));const X=unit([Math.sin(x),Math.cos(x),.4]);for(let t=0;t<=1;t+=.05)denomMin=Math.min(denomMin,norm(add(scale(noFixedMap(X),1-t),scale(X,-t))))}
 const measured=Array.from({length:6},(_,n)=>coefficients(n));const expected=[[.6,0],[1,0],[0,.65],[.35,0],[0,0],[0,.25]];const coefficientError=Math.max(...measured.flatMap((v,n)=>v.map((x,k)=>Math.abs(x-expected[n][k]))));
 if(actionErr>1e-12||coefficientError>1e-10||denomMin<.5)throw Error('Analytic model failure');
 return {passed:true,puzzle:{legalMoves:moves,solvedInvariant:1,swappedInvariant:invariant(swapped),edgeGeneratorsInvolutions:true},chirality:{properRotationDeterminant:det([[1,0,0],[0,1,0],[0,0,1]]),swappedColorsDeterminant:det([[0,1,0],[1,0,0],[0,0,1]])},quaternions:{maxAssociativityOrNormError:err},octonions:{left,right,associative:false},sphere:{sampleHomotopyDenominatorMinimum:denomMin,evenAntipodalDegree:-1,oddAntipodalDegree:1},fourier:{actionError:actionErr,coefficientError,measured,initialSecondComponentOnly:0,convergenceClaim:'L2; completeness is an external input'}}}
 return {dot,norm,add,scale,unit,identity,sign,invariant,neighbors,slide,edgeAction,walk,rotate,det,qmul,qconj,omul,basis,rotatePair,signal,coefficients,partial,noFixedMap,homotopy,cube,cubeTurn,cubeSequence,audit};
})();
if(typeof module!=='undefined')module.exports=ActionMath;
