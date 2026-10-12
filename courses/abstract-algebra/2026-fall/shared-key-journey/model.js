// Educational ECDH + HKDF + AES-GCM. The small group and fixed scalars are
// deliberately inspectable teaching data, NOT cryptographic security parameters.
const CryptoLesson = (() => {
  const p = 251, mod = n => ((n % p) + p) % p;
  const inv = n => { let a=mod(n), e=p-2, v=1; while(e){if(e&1)v=mod(v*a);a=mod(a*a);e>>=1;}return v; };
  function add(P,Q) {
    if(!P)return Q && [...Q]; if(!Q)return [...P];
    if(P[0]===Q[0] && mod(P[1]+Q[1])===0)return null;
    const l=P[0]===Q[0] ? mod(3*P[0]*P[0]*inv(2*P[1])) : mod((Q[1]-P[1])*inv(Q[0]-P[0]));
    const x=mod(l*l-P[0]-Q[0]);return [x,mod(l*(P[0]-x)-P[1])];
  }
  function mul(n,P){let out=null,q=P;while(n){if(n&1)out=add(out,q);q=add(q,q);n=Math.floor(n/2);}return out;}
  const points=[];for(let x=0;x<p;x++)for(let y=0;y<p;y++)if(mod(y*y-x*x*x-7)===0)points.push([x,y]);
  let G=null,order=0;
  for(const P of points.slice(0,40)){let q=P,n=1;while(q&&n<400){q=add(q,P);n++;}if(!q&&n>order){G=P;order=n;}}
  const k=7,r=13,Q=mul(k,G),R=mul(r,G),senderS=mul(r,Q),receiverS=mul(k,R);
  const hex=b=>Array.from(b,x=>x.toString(16).padStart(2,'0')).join('');
  const bits=b=>b.toString(2).padStart(8,'0');
  const equal=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
  const message='明天下午三点见。';
  const data={p,points,G,order,k,r,Q,R,senderS,receiverS,message,add,mul,bits,hex};
  async function prepare(){
    if(!equal(senderS,receiverS))throw Error('ECDH shared point mismatch');
    const utf=new TextEncoder(),salt=utf.encode('Shared key lesson / fixed teaching salt');
    // Public context is identical at both ends; this is an explanatory construction,
    // not a claim to implement the exact HPKE protocol/key schedule.
    const info=utf.encode('ECDH lesson / Q='+Q.join(',')+' / R='+R.join(','));
    async function derive(S){
      const ikm=await crypto.subtle.importKey('raw',new Uint8Array([S[0]]),'HKDF',false,['deriveBits']);
      return new Uint8Array(await crypto.subtle.deriveBits({name:'HKDF',hash:'SHA-256',salt,info},ikm,256));
    }
    const [senderK,receiverK]=await Promise.all([derive(senderS),derive(receiverS)]);
    const nonce=new Uint8Array([0x10,0x20,0x30,0x40,0x50,0x60,0x70,0x80,0x90,0xa0,0xb0,0xc0]);
    const plaintext=utf.encode(message),aad=utf.encode('Xiaoming -> you / lesson 1');
    const keyA=await crypto.subtle.importKey('raw',senderK,'AES-GCM',false,['encrypt']);
    const keyB=await crypto.subtle.importKey('raw',receiverK,'AES-GCM',false,['decrypt']);
    const params={name:'AES-GCM',iv:nonce,additionalData:aad,tagLength:128};
    const sealed=new Uint8Array(await crypto.subtle.encrypt(params,keyA,plaintext));
    const ciphertext=sealed.slice(0,-16),tag=sealed.slice(-16);
    const recovered=new Uint8Array(await crypto.subtle.decrypt(params,keyB,sealed));
    const changed=new Uint8Array(sealed);changed[0]^=1;
    let rejectsTamper=false;try{await crypto.subtle.decrypt(params,keyB,changed);}catch{rejectsTamper=true;}
    // GCM encrypts using a counter-mode keystream: c XOR m recovers that stream
    // for this teaching transcript, so the animated byte is an actual AES-GCM byte.
    const stream=plaintext.map((b,i)=>b^ciphertext[i]);
    Object.assign(data,{senderK,receiverK,nonce,plaintext,ciphertext,tag,sealed,recovered,stream,rejectsTamper,
      keyText:hex(senderK).slice(0,16),cipherText:hex(ciphertext),nonceText:hex(nonce),tagText:hex(tag)});
    return data;
  }
  function audit(){
    let cases=0;for(let a=1;a<=24;a++)for(let b=1;b<=24;b++){
      if(!equal(mul(a,mul(b,G)),mul(b,mul(a,G))))throw Error('Scalar commutation failure');cases++;
    }
    return {curve:'y²=x³+7 over F_251',groupSize:points.length+1,basePoint:G,order,k,r,Q,R,
      senderS,receiverS,sharedPointEqual:equal(senderS,receiverS),scalarCases:cases,
      derivedKeysEqual:equal(Array.from(data.senderK),Array.from(data.receiverK)),
      decryptionMatches:equal(Array.from(data.plaintext),Array.from(data.recovered)),
      rejectsTamper:data.rejectsTamper,plaintext:message,cipherHex:data.cipherText,
      packetFields:['R','nonce','ciphertext','tag','public authenticated context'],
      privateFieldsNeverSent:['k','r','S','K','keystream'],
      limitation:'Small finite group and fixed scalars/nonce for a single teaching transcript; not secure messaging or an exact HPKE implementation.'};
  }
  return {...data,data,prepare,audit};
})();
let DEMO=null;
const DEMO_READY=CryptoLesson.prepare().then(x=>{DEMO=x;return x;});
