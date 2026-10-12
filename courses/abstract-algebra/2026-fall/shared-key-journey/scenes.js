// The visual vocabulary is inherited from the existing algebra promo.
const C_GOLD='255,209,102',C_TEAL='90,255,220',C_PINK='255,126,182',C_BLUE='140,200,255';
const COL={gold:'#ffda88',teal:'#a2ffe4',pink:'#ffb5d4',blue:'#b4daff',dim:'#b8c5ca'};
function ink(points,color=C_TEAL,alpha=1,width=2.4,closed=false){
  if(points.length<2||alpha<=0)return;
  ctx.save();ctx.globalCompositeOperation='lighter';ctx.lineCap='round';ctx.lineJoin='round';
  for(const [w,a]of[[width*6,.055],[width*2.5,.18],[width,.9]]){
    ctx.beginPath();points.forEach((p,i)=>ctx[i?'lineTo':'moveTo'](p[0],p[1]));if(closed)ctx.closePath();
    ctx.strokeStyle=`rgba(${color},${a*alpha})`;ctx.lineWidth=w;ctx.stroke();
  }ctx.restore();
}
function bead(p,color=C_TEAL,alpha=1,radius=30){ctx.save();ctx.globalCompositeOperation='lighter';glowDot(p[0],p[1],radius,`rgba(${color},A)`,alpha);ctx.restore();}
function small(s,x,y,color=COL.dim,size=30,alpha=1,font=F_ZH){text(s,x,y,{size,color,alpha,font});}
function eq(s,y=225,size=60,alpha=1,x=960,color=COL.teal){text(s,x,y,{font:F_MATH,size,color,alpha,glow:'rgba(90,255,220,.3)',blur:22});}
function cosmos(t,tint=[.08,.25,.31]){glDraw(0,{time:t+70,tint,amp:.45});starfield(t,.12,3);}
function arrow(a,b,color=C_TEAL,alpha=1){ink([a,b],color,alpha,2.3);const d=Math.atan2(b[1]-a[1],b[0]-a[0]);ink([[b[0]-14*Math.cos(d-.4),b[1]-14*Math.sin(d-.4)],b,[b[0]-14*Math.cos(d+.4),b[1]-14*Math.sin(d+.4)]],color,alpha,2.3);}
function lineBox(x,y,w,h,color=C_BLUE,alpha=1){
  ctx.save();ctx.globalAlpha=alpha;ctx.fillStyle='rgba(0,8,14,.56)';ctx.beginPath();ctx.roundRect(x-w/2,y-h/2,w,h,18);ctx.fill();ctx.strokeStyle=`rgba(${color},.35)`;ctx.lineWidth=1.5;ctx.stroke();ctx.restore();
}
function lock(x,y,color=C_GOLD,a=1,size=1){
  ctx.save();ctx.translate(x,y);ctx.scale(size,size);
  const arc=Array.from({length:35},(_,i)=>[30*Math.cos(PI+PI*i/34),-20+36*Math.sin(PI+PI*i/34)]);ink(arc,color,a,2.3);
  lineBox(0,13,85,68,color,a);bead([0,6],color,a,12);ink([[0,10],[0,29]],color,a,3);ctx.restore();
}
function roles(a=1){
  small('你 · 接收者',330,320,COL.gold,38,a);small('小明 · 发送者',1590,320,COL.teal,38,a);
  ink([[160,357],[500,357]],C_GOLD,a*.45,1.3);ink([[1420,357],[1760,357]],C_TEAL,a*.45,1.3);
}
function secret(label,x,y,color=C_GOLD,a=1){lock(x,y-45,color,a,.8);small(label,x,y+35,color===C_GOLD?COL.gold:COL.pink,38,a,F_MATH);small('留在本地',x,y+90,COL.dim,27,a);}
function pointText(P){return P?'('+P.join(', ')+')':'O';}
function pointCloud(t,{x=960,y=570,size=520,marks=[],alpha=.55}={}){
  const at=P=>[x+(P[0]/250-.5)*size,y-(P[1]/250-.5)*size*.72];
  ink([[x-size/2,y+size*.36],[x+size/2,y+size*.36]],C_BLUE,.18,1);
  ink([[x-size/2,y-size*.36],[x-size/2,y+size*.36]],C_BLUE,.18,1);
  for(let i=0;i<DEMO.points.length;i++){
    const p=at(DEMO.points[i]);ctx.fillStyle=`rgba(160,208,255,${alpha*(.4+.18*Math.sin(t*.5+i))})`;ctx.fillRect(p[0]-1.6,p[1]-1.6,3.2,3.2);
  }
  for(const m of marks){const p=at(m.P);bead(p,m.color||C_TEAL,m.a??1,32);small(m.name,p[0]+(m.dx??30),p[1]+(m.dy??-32),m.col||COL.teal,31,m.a??1,F_MATH);}
  small('y² = x³ + 7  (mod 251)',x,y+size*.36+36,COL.blue,25,alpha,F_MATH);
  small('教学小群 · 不用于安全通信',x,y+size*.36+75,COL.dim,23,alpha);
  return at;
}
function travel(t,start,end,a,b,label,color=C_TEAL){
  const f=eio(clamp((t-start)/(end-start))),p=[lerp(a[0],b[0],f),lerp(a[1],b[1],f)];
  arrow(a,b,color,.23);bead(p,color,win(t,start-.5,end+1,.5,.5),38);
  if(label)small(label,p[0],p[1]-48,color===C_GOLD?COL.gold:COL.teal,37,win(t,start-.5,end+1,.5,.5),F_MATH);
}
function sharedStamp(x,y,alpha=1){lineBox(x,y,410,115,C_TEAL,alpha);eq('S',y-12,54,alpha,x);small(Array.from(DEMO.stream.slice(0,2),CryptoLesson.bits).join(' ')+'…',x,y+32,COL.teal,21,alpha,F_MONO);}
function pointToBits(lt,x=960,y=405,start=.7,end=3){
  const f=sstep(start,end,lt),str=Array.from(DEMO.stream.slice(0,2),CryptoLesson.bits).join('');
  bead([x,y],C_GOLD,.6*(1-f),70);eq('S',y-12,64,1-f,x,COL.gold);
  for(let i=0;i<16;i++){
    const dx=x-285+i*38,from=[x+14*Math.cos(i*TAU/16),y+14*Math.sin(i*TAU/16)];
    const p=[lerp(from[0],dx,eio(f)),lerp(from[1],y,eio(f))];
    bead(p,C_TEAL,.45*Math.sin(PI*f),18);
    small(str[i],dx,y,COL.teal,31,sstep(.45,1,f),F_MONO);
  }
  small(f>.95?'S：二进制串（仍用同一个符号）':'S：群里的点',x,y+52,COL.blue,26);
}
function binarySum(lt,{decrypt=false,start=5.4,end=12,y=550}={}){
  const a=decrypt?DEMO.ciphertext[0]:DEMO.plaintext[0],b=DEMO.stream[0],out=a^b;
  const A=CryptoLesson.bits(a),B=CryptoLesson.bits(b),O=CryptoLesson.bits(out);
  const f=clamp((lt-start)/(end-start))*8,active=Math.min(7,Math.floor(f));
  bitRow(decrypt?'密文 c':'消息 m',a,y,decrypt?COL.pink:COL.gold,sstep(start-2,start-1,lt));
  bitRow('二进制串 S',b,y+95,COL.teal,sstep(start-1.7,start-.5,lt));
  small(decrypt?'恢复 m = c + S':'密文 c = m + S',380,y+190,COL.pink,31,sstep(start-.3,start,lt));
  for(let i=0;i<8;i++){
    const x=740+i*65,done=lt>=start+(i+.72)/8*(end-start);
    lineBox(x,y+190,52,58,decrypt?C_GOLD:C_PINK,sstep(start-.3,start,lt));
    small(done?O[i]:'·',x,y+190,done?(decrypt?COL.gold:COL.pink):COL.dim,35,sstep(start-.3,start,lt),F_MONO);
    small('+',x,y+48,COL.teal,23,sstep(start-.4,start,lt),F_MATH);
    small('=',x,y+143,COL.teal,23,sstep(start-.4,start,lt),F_MATH);
    if(!decrypt)small('ℤ/2ℤ',x,852,COL.blue,19,sstep(start+.3,start+1,lt),F_MATH);
    if(lt>=start&&lt<end&&i===active){
      ctx.save();ctx.strokeStyle='rgba(255,218,135,.85)';ctx.fillStyle='rgba(255,218,135,.07)';ctx.lineWidth=2;
      ctx.beginPath();ctx.roundRect(x-30,y-36,60,260,12);ctx.fill();ctx.stroke();ctx.restore();
    }
  }
  if(lt>=start){
    const formula=lt<end?A[active]+' + '+B[active]+' = '+O[active]+'  (mod 2)':(decrypt?'S + S = 0':'逐位相加，不进位');
    eq(formula,decrypt?665:802,decrypt?32:38,1,decrypt?1550:960);
  }
}
function bitRow(label,byte,y,color,reveal=1){
  small(label,380,y,color,30,reveal);const str=CryptoLesson.bits(byte);
  for(let i=0;i<8;i++){const a=sstep(i*.09,i*.09+.25,reveal);lineBox(740+i*65,y,52,58,color===COL.gold?C_GOLD:color===COL.pink?C_PINK:C_TEAL,a);small(str[i],740+i*65,y,color,35,a,F_MONO);}
}
function reg(start,len,zh,en,draw,subs,sfx=[]){scene({start,len,ch:[String(SC.length+1).padStart(2,'0'),zh,en],fi:.45,fo:.45,mb:2,cam:()=>({z:1}),draw,subs,sfx});}

// What each participant has actually received or computed at this point.
// Curves are agreed first; the first packet explicitly supplies BOTH Q and G.
const LEARN={q:5*BAR+9.8,interceptPublic:11*BAR+3.5,publicPoints:11*BAR+7,r:15*BAR+1.8,R:15*BAR+5,S:15*BAR+9.5,
  senderBits:21*BAR+3,nonce:21*BAR+4.5,cipher:21*BAR+12,tag:21*BAR+12.2,
  interceptCipher:27*BAR+3.5,packet:27*BAR+8,receiverS:32*BAR+9.5,receiverBits:38*BAR+2,message:38*BAR+10.2};
function knowledgeAt(t){
  const you=['k','G'],xiaoming=['m'],hacker=[];
  if(t>=LEARN.interceptPublic)hacker.push('G','Q');
  if(t>=LEARN.interceptCipher)hacker.push('R','N','c','tag');
  if(t>=LEARN.q)you.push('Q');
  if(t>=LEARN.publicPoints)xiaoming.push('G','Q');
  if(t>=LEARN.r)xiaoming.push('r');
  if(t>=LEARN.R)xiaoming.push('R');
  if(t>=LEARN.S)xiaoming.push('S');
  if(t>=LEARN.nonce)xiaoming.push('N');
  if(t>=LEARN.cipher)xiaoming.push('c');
  if(t>=LEARN.tag)xiaoming.push('tag');
  if(t>=LEARN.packet)you.push('R','N','c','tag');
  if(t>=LEARN.receiverS)you.push('S');
  if(t>=LEARN.message)you.push('m');
  return {you:{known:you,unknown:['r','S','m'].filter(x=>!you.includes(x)),sForm:t>=LEARN.receiverBits?'binary':'point'},
    xiaoming:{known:xiaoming,unknown:['k','G','Q','S'].filter(x=>!xiaoming.includes(x)),rNotChosen:t<LEARN.r,sForm:t>=LEARN.senderBits?'binary':'point'},
    hacker:{known:hacker,unknown:['k','r','S','m'],passive:true},
    publicPointPacket:['Q','G'],pointElements:['G','Q','R','S'],integerScalars:['k','r'],binaryData:['S (after conversion)','c','tag']};
}
function knowledge(T){
  if(T<1)return;
  const state=knowledgeAt(T),alpha=win(T,1,TOTAL-.3,.7,.5);
  const decoding=T>=38*BAR&&T<44*BAR,y=decoding?280:386;
  for(const [x,label,s,color]of[[330,'你',state.you,COL.gold],[1590,'小明',state.xiaoming,COL.teal]]){
    small(label+'已知：'+s.known.join('、'),x,y,color,25,alpha);
    small('不知道：'+s.unknown.join('、'),x,y+(decoding?31:37),COL.dim,23,alpha);
  }
  small('黑客 · 旁观者',1660,65,COL.pink,25,alpha);
  small('截获：'+(state.hacker.known.join('、')||'尚无数据'),1660,96,COL.pink,22,alpha);
  small('不知道：k、r、S、m',1660,125,COL.dim,22,alpha);
}
function interception(lt,start,end,packet,y=650){
  const a=win(lt,start,end,.5,.5);if(a<=0)return;
  const f=clamp((lt-start)/(end-start));
  ink([[960,y-95],[960,y-37]],C_PINK,a*.35,1.7);
  bead([960,y-95+58*f],C_PINK,a,19);
  lineBox(960,y,570,85,C_PINK,a);
  small('黑客同时截获：'+packet,960,y,COL.pink,29,a);
}

reg(0,5,'一个秘密，两个陌生人','ONE SECRET, TWO PEOPLE',lt=>{
  cosmos(lt);titleWord('不传钥匙，共享秘密',960,252,72,lt,.5,.08,7,1,.18);roles(sstep(1.8,2.8,lt));
  lock(330,515,C_GOLD,sstep(3,4,lt),1.2);small('私钥 k',330,640,COL.gold,42,sstep(3,4,lt),F_MATH);
  lineBox(1510,520,530,170,C_TEAL,sstep(3.5,4.5,lt));small('明天下午三点见。',1510,505,COL.teal,39,sstep(3.5,4.5,lt));eq('消息 m',575,33,sstep(3.5,4.5,lt),1510);
  eq('目标：双方算出同一个共享秘密 S',800,46,sstep(7,8,lt));
},[[.6,4.4,'你保管私钥，小明要给你发一条秘密消息。','You keep the private key. Xiaoming wants to send you a secret.'],[4.6,8,'消息是 m；私钥 k 不是消息。','The message is m. Your private key k is not the message.'],[8.2,12.9,'重点：双方算出同一个 S，却不发送 S。','Both compute the same S without sending S itself.']],[[.8,'swell',{dur:2}],[3.3,'ding',{midi:74}],[7.6,'shimmer']]);

reg(5,6,'你生成自己的公钥','YOUR PUBLIC KEY',lt=>{
  if(lt>=9.5){
    cosmos(lt);const a=sstep(9.5,10,lt);
    eq('实战：随机取 k ∈ {1, 2, …, q − 1}',242,58,a);
    small('q = ord(G)：大素数阶子群的阶',960,360,COL.blue,35,a,F_MATH);
    eq('q ≈ 2²⁵⁶',425,58,a);
    lineBox(510,600,720,230,C_GOLD,a);lineBox(1410,600,720,230,C_PINK,a);
    small('已知 G、k，正向计算',510,520,COL.gold,34,a);eq('Q = kG',590,53,a,510,COL.gold);small('几百次点运算',510,675,COL.gold,36,a);
    small('已知 G、Q，反求私钥',1410,520,COL.pink,34,a);eq('寻找 k：kG = Q',590,48,a,1410,COL.pink);small('约 2¹²⁸ 次点运算',1410,675,COL.pink,36,a);
    small('适当选群、均匀随机私钥 · 经典计算机的通用攻击量级',960,790,COL.blue,28,a);
    small('k = 200 或本片的小群，可以轻易搜索；它们只是教学示例。',960,860,COL.dim,29,a);return;
  }
  cosmos(lt);eq('你在本地计算：Q = kG',242,65);roles();secret('k = 7',330,585,C_GOLD);small('私钥：只有你持有',330,765,COL.gold,29);
  const f=eio(clamp((lt-3)/6)),idx=Math.min(DEMO.k,Math.floor(f*DEMO.k));
  const marks=[{P:DEMO.G,name:'G',color:C_BLUE,col:COL.blue,dx:35,dy:28},{P:DEMO.Q,name:'Q',color:C_TEAL}];
  const at=pointCloud(lt,{marks});const P=CryptoLesson.mul(Math.max(1,idx),DEMO.G);bead(at(P),C_GOLD,win(lt,3,10,.3,.3),30);
  small('小明尚未收到 Q、G',1570,485,COL.dim,33);small('他只知道自己要发的消息 m',1570,560,COL.teal,27);
  small('G、Q：群里的点',1570,655,COL.blue,31);small('k：整数',1570,715,COL.gold,31);
},[[.6,4.5,'曲线已约定，G 是你选用的公开基点。','The curve is agreed. G is the public base point you use.'],[4.8,9.2,'你用私钥 k，在本地计算点 Q = kG。','Use your private scalar k to compute Q = kG locally.'],[9.5,12.2,'实战在巨大范围中随机取 k；不会只选 200 这样的小数。','In practice k is random over a huge range, not a tiny number like 200.'],[12.5,15.5,'正向计算快，反求 k 难。接下来只发送 Q、G。','Forward computation is fast; finding k is hard. Send only Q and G.']],[[2,'blip',{midi:74}],[3.3,'glide',{dur:5}],[9.6,'ding',{midi:81}]]);

reg(11,4,'发送两个公开的点','SEND TWO PUBLIC POINTS',lt=>{
  cosmos(lt);eq('你 → 小明：发送 Q、G',242,62);roles();secret('私钥 k · 不发送',330,690,C_GOLD);
  arrow([470,495],[1450,495],C_TEAL,.25);
  const f=eio(clamp((lt-2)/5)),x=lerp(430,1490,f),a=win(lt,1.5,7.8,.4,.4);
  lineBox(x,485,320,130,C_TEAL,a);eq('Q、G',475,50,a,x);small('两个群里的点',x,520,COL.blue,23,a);
  eq('收到 Q、G',480,40,sstep(7,7.6,lt),1590);small('仍然不知道 k',1590,675,COL.teal,37,sstep(7,7.8,lt));
  interception(lt,3.5,10.2,'Q、G');
  small('发送的是两个点；没有发送私钥或计算等式。',960,805,COL.blue,32,sstep(7,8,lt));
},[[.6,4,'你发送两个点 Q、G，私钥 k 留在本地。','Send the two points Q and G. Keep k private.'],[4.3,10.1,'收到后，小明知道 Q、G，仍不知道 k。','After receiving them, Xiaoming knows Q and G, but not k.']],[[2,'whoosh',{dur:4.8}],[7.1,'chime',{midi:81}]]);

reg(15,6,'小明准备一个临时秘密','XIAOMING CHOOSES AN EPHEMERAL SECRET',lt=>{
  cosmos(lt);roles();eq('小明在本地算：R = rG，S = rQ',242,56);secret('r = 13',1590,690,C_PINK,sstep(1,2,lt));
  small('你保管 k',330,520,COL.gold,36);small('暂时还不知道 S',330,600,COL.dim,30);
  pointCloud(lt,{marks:[{P:DEMO.G,name:'G',color:C_BLUE,col:COL.blue,dy:28},{P:DEMO.Q,name:'Q',color:C_TEAL},
    {P:DEMO.R,name:'R',color:C_PINK,col:COL.pink,a:sstep(3.5,5,lt),dx:-38,dy:34},
    {P:DEMO.senderS,name:'S',color:C_GOLD,col:COL.gold,a:sstep(8,9.5,lt),dx:35,dy:32}]});
  eq('R = '+pointText(DEMO.R),490,34,sstep(4,5,lt),1590,COL.pink);eq('S = '+pointText(DEMO.senderS),550,34,sstep(9,10,lt),1590,COL.gold);
},[[.6,4.6,'小明秘密选一个新的随机整数 r。','Xiaoming privately chooses a fresh random scalar r.'],[4.9,8.1,'他算出 R = rG，准备把这个点发给你。','He computes R = rG, a point to send to you.'],[8.4,15.4,'再用你的公钥，算出共享点 S = rQ。','Using your public key, he computes the shared point S = rQ.']],[[1.7,'blip',{midi:76}],[4.7,'pop',{midi:81}],[9,'ding',{midi:86}]]);

reg(21,6,'点变成串，在直积群中相加','FROM A POINT TO ADDITION IN A PRODUCT GROUP',lt=>{
  cosmos(lt,[.12,.19,.29]);eq('S 变成二进制串，然后 c = m + S',242,55);
  pointToBits(lt);small('同一个符号 S，随动画由点变成串',960,335,COL.blue,28);
  binarySum(lt);
  small('1 + 1 = 0',1510,590,COL.gold,40,sstep(5.4,6.5,lt),F_MATH);
  small('每一位都在 ℤ/2ℤ 中相加',1510,645,COL.blue,27,sstep(5.4,6.5,lt));
  small('不向相邻一位进位',1510,705,COL.dim,26,sstep(6,7,lt));
  eq('m、S、c ∈ (ℤ/2ℤ)ⁿ，n = '+String(DEMO.plaintext.length*8)+'  ·  展示前 8 位',899,30,sstep(3.5,4.5,lt));
},[[.6,3.9,'把群里的点 S 转换成二进制串，仍记作 S。','Convert the shared point into a binary string, still called S.'],[4.2,7.1,'消息 m 和 S，都在多个 ℤ/2ℤ 的直积群里。','Both m and S belong to a product of copies of Z/2Z.'],[7.4,11.9,'逐位做模二加法：1 + 1 = 0，不进位。','Add modulo two in each coordinate: 1 + 1 = 0, with no carry.'],[12.2,15.5,'得到密文 c = m + S，发出 c，不发出 S。','The ciphertext is c = m + S. Send c, keep S secret.']],[[2.6,'crystal'],[5.4,'data',{dur:6.6}],...Array.from({length:8},(_,i)=>[5.4+i*.825,'tick',{gain:.55}]),[12,'ding',{midi:84}]]);

reg(27,5,'真正穿过通道的是什么','WHAT ACTUALLY CROSSES THE CHANNEL',lt=>{
  cosmos(lt);eq('小明 → 你：R、编号 N、密文 c、校验标签 tag',242,51);roles();secret('你的私钥 k',330,655,C_GOLD);secret('小明的随机数 r',1590,655,C_PINK);
  const f=eio(clamp((lt-2)/6)),x=lerp(1490,430,f);arrow([1400,470],[520,470],C_BLUE,.35);
  lineBox(x,470,400,140,C_TEAL,win(lt,1.5,10,.5,.5));eq('R   N   c   tag',445,36,win(lt,1.5,10,.5,.5),x);
  small(DEMO.cipherText.slice(0,24)+'…',x,505,COL.pink,22,win(lt,1.5,10,.5,.5),F_MONO);
  interception(lt,3.5,12.8,'R、N、c、tag',605);
  small('R：群里的点     c、tag：二进制数据',960,790,COL.blue,32,sstep(5.2,6.2,lt));
  small('收到 R 后，你仍需自己计算 S。',960,850,COL.gold,34,sstep(8.8,9.6,lt));
},[[.6,4.9,'小明把 R、编号、密文和校验标签发给你。','Xiaoming sends R, the nonce, ciphertext, and authentication tag.'],[5.2,8.8,'R 是群里的点；c 和 tag 是二进制数据。','R is a group point. The ciphertext and tag are binary data.'],[9.1,12.8,'你收到这些数据，但还没有算出共享秘密 S。','You have received the packet, but have not yet computed S.']],[[2,'whoosh',{dur:5.8}],[8,'chime',{midi:81}],[9.4,'shimmer']]);

reg(32,6,'两条路径，同一个共享点','TWO PATHS, THE SAME SHARED POINT',lt=>{
  cosmos(lt);roles();eq('你：kR       小明：rQ',242,63);
  secret('k',330,560,C_GOLD);secret('r',1590,560,C_PINK);
  eq('kR = k(rG)',710,47,sstep(2,3,lt),420,COL.gold);eq('rQ = r(kG)',710,47,sstep(2,3,lt),1500,COL.teal);
  const f=eio(clamp((lt-4)/5));travel(lt,4,9,[550,555],[905,555],'kR',C_GOLD);travel(lt,4,9,[1370,555],[1015,555],'rQ',C_TEAL);
  bead([960,555],C_TEAL,.45*sstep(8.5,9.5,lt),60);eq('S',555,75,sstep(9,10,lt));
  eq('k(rG) = (kr)G = r(kG)',780,59,sstep(8,9,lt));small('相同的共享点 S = '+pointText(DEMO.senderS),960,850,COL.teal,32,sstep(10,11,lt));small('本地计算，不发送 S',960,889,COL.dim,22,sstep(10.5,11.5,lt));
},[[.6,4.5,'你收到 R，用自己的私钥计算 kR。','You receive R and multiply it by your private scalar k.'],[4.8,9,'小明算 rQ；你算 kR。两条路径在同一点相遇。','Xiaoming computes rQ. You compute kR. Both reach the same point.'],[9.3,15.5,'因为 k(rG) = r(kG)，你们得到同一个 S。','Since k(rG) = r(kG), both of you obtain the same S.']],[[4,'glide',{dur:5}],[9.1,'ring',{dur:3}],[10.2,'success']]);

reg(38,6,'再加一次 S，读回原消息','ADD S AGAIN TO RECOVER THE MESSAGE',lt=>{
  cosmos(lt);eq('c + S = (m + S) + S = m',242,61);
  if(lt<2.2)pointToBits(lt,460,390,.3,2);else sharedStamp(460,390);
  sharedStamp(1460,390);eq('=',390,72,sstep(1.7,2.2,lt));small('你算出的 S',460,490,COL.gold,32);small('小明算出的 S',1460,490,COL.teal,32);
  binarySum(lt,{decrypt:true,start:5,end:9.5,y:565});
  small('在 (ℤ/2ℤ)ⁿ 中，S + S = 0',1540,715,COL.teal,27,sstep(7,8,lt),F_MATH);
  lineBox(960,848,860,76,C_GOLD,sstep(10,11,lt));small('明天下午三点见。',960,848,COL.gold,40,sstep(10,11,lt));
},[[.6,4.5,'相同的共享点，转换成相同的二进制串 S。','The same shared point yields the same binary string S.'],[4.8,9.2,'再逐位加一次 S；每一位的 1 + 1 都等于 0。','Add S once more. In each coordinate, 1 + 1 equals zero.'],[9.5,15.5,'因为 S + S = 0，所以 c + S = m，读回原消息。','Since S + S = 0, c + S = m recovers the message.']],[[1.5,'chime',{midi:86}],[4.6,'data',{dur:4.9}],[10.2,'success']]);

reg(44,5.5,'秘密没有被传送','A SHARED KEY THAT WAS NEVER SENT',lt=>{
  cosmos(lt,[.15,.20,.31]);titleWord('不传私钥，共享秘密',960,252,72,lt,.5,.08,6,1,.12);
  roles();lock(330,535,C_GOLD,1,1.1);lock(1590,535,C_PINK,1,1.1);eq('k',635,55,1,330,COL.gold);eq('r',635,55,1,1590,COL.pink);
  sharedStamp(960,560,sstep(1,2,lt));ink([[420,490],[755,535]],C_GOLD,.35,2);ink([[1500,490],[1165,535]],C_TEAL,.35,2);
  eq('加密：c = m + S     解密：m = c + S',735,49,sstep(2,3,lt));small('二进制串的加法，就是多个 ℤ/2ℤ 的直积群运算。',960,825,COL.teal,33,sstep(3,4,lt));
  small('黑客有 G、Q、R、c；缺少 k、r，不能直接算出 S。',960,882,COL.pink,27,sstep(4,5,lt));
},[[.6,4.8,'小明不知道你的 k，你也不知道小明的 r。','Xiaoming never learns k. You never learn r.'],[5.1,9,'黑客截获公开数据，却没有你们的私钥和 S。','The observer sees public data, but not the private scalars or S.'],[9.3,13.9,'双方得到同一个 S，私钥始终保密。','Both obtain the same S. The private scalars stay secret.']],[[1.5,'swell',{dur:2}],[3,'ring',{dur:3}]]);

window.__modelAudit=()=>CryptoLesson.audit();
window.__knowledgeAt=knowledgeAt;
window.__learningTimes=()=>LEARN;
window.__binaryAudit=()=>({dimension:DEMO.plaintext.length*8,
  truthTable:[[0,0,0],[0,1,1],[1,0,1],[1,1,0]],
  additionWorks:DEMO.plaintext.every((m,i)=>(m^DEMO.stream[i])===DEMO.ciphertext[i]),
  cancellationWorks:DEMO.ciphertext.every((c,i)=>(c^DEMO.stream[i])===DEMO.plaintext[i]),
  selfAdditionZero:DEMO.stream.every(x=>(x^x)===0),sameNotationAfterConversion:'S',
  firstByte:{m:CryptoLesson.bits(DEMO.plaintext[0]),S:CryptoLesson.bits(DEMO.stream[0]),c:CryptoLesson.bits(DEMO.ciphertext[0])}});
window.__chapters=()=>SC.map(s=>({start:s.start*BAR,duration:s.len*BAR,title:s.ch[1],english:s.ch[2],subtitles:s.subs}));
