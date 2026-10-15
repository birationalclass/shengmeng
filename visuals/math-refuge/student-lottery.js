// Private rosters never leave this browser. Only the last two ID digits are retained.
import {SCREEN_FONT,SCREEN_MONO} from './smart-screen-style.js';
export const LOTTERY_RECT=[1100,180,396,280],LOTTERY_HANDLE=[1445,290],LOTTERY_ROSTER=[1268,450];
export const SLOT_SPIN_SECONDS=2.8;
export function slotReels(digits,age){
 return [...digits].map((digit,i)=>{const target=Number(digit),start=(target+3+i*2)%10,distance=40+i*10+(target-start+10)%10,duration=i?SLOT_SPIN_SECONDS:2.15,t=Math.max(0,Math.min(1,age/duration)),position=start+distance*(1-Math.pow(1-t,3));return{position,digit:Math.floor(position+1e-8)%10,settled:t===1};});
}
export function parseRoster(text){
 let values;try{values=JSON.parse(text);values=Array.isArray(values)?values:values.students||values.roster;}catch{const lines=text.replace(/^\uFEFF/,'').trim().split(/\r?\n/).map(l=>l.split(/[,\t]/).map(s=>s.trim().replace(/^"|"$/g,'')));const head=lines.shift(),id=head.findIndex(s=>/学号|student.?id|^id$|suffix/i.test(s)),name=head.findIndex(s=>/姓名|name/i.test(s));if(id<0||name<0)throw Error('名单需要学号和姓名两列');values=lines.map(l=>({id:l[id],name:l[name]}));}
 if(!Array.isArray(values)||!values.length)throw Error('花名册为空');const seen=new Set(),rows=[];
 for(const row of values){const id=String(row.id??row.studentId??row.学号??row.suffix??'').trim(),name=String(row.name??row.姓名??'').trim(),key=(row.key!==undefined?'key:'+row.key:id+'\0'+name);if(!/\d{2}$/.test(id)||!name||name.length>30)throw Error('请核对学号与姓名');if(seen.has(key))continue;seen.add(key);rows.push({suffix:id.slice(-2),name,key:row.key??rows.length});}
 return rows;
}
const secureIndex=n=>{const v=new Uint32Array(1),limit=Math.floor(4294967296/n)*n;do{crypto.getRandomValues(v);}while(v[0]>=limit);return v[0]%n;};
export function createStudentLottery({storage=globalThis.localStorage,randomIndex=secureIndex,now=()=>performance.now()/1000,today=()=>new Date().toLocaleDateString('en-CA')}={}){
 let course='',lesson='',roster=[],used={},draws=new Map(),revision=0,error='';const storageKey=id=>'refuge-roster-v1:'+id;
 const usedKey=()=> 'refuge-called-v1:'+course,lessonKey=()=>lesson+':'+today();
 function setCourse(id,nextLesson=id){if(id!==course){course=id;error='';try{const saved=storage?.getItem(storageKey(id));roster=saved?parseRoster(saved):[];used=JSON.parse(storage?.getItem(usedKey())||'{}');}catch{roster=[];used={};}}if(nextLesson!==lesson){lesson=nextLesson;draws.clear();revision++;}}
 function importRoster(text){const parsed=parseRoster(text);storage?.setItem(storageKey(course),JSON.stringify(parsed));roster=parsed;used={};storage?.removeItem(usedKey());draws.clear();error='';revision++;return roster.length;}
 const remaining=()=>roster.filter(r=>!(used[lessonKey()]||[]).includes(r.key));
 function pick(){const candidates=remaining();if(!candidates.length)return null;const student=candidates[randomIndex(candidates.length)];(used[lessonKey()]??=[]).push(student.key);storage?.setItem(usedKey(),JSON.stringify(used));return student;}
 function spin(key){if(!roster.length)return false;const prior=draws.get(key);if(prior&&now()-prior.start<SLOT_SPIN_SECONDS)return false;const student=pick();if(!student)return false;draws.set(key,{student,start:now()});revision++;return true;}
 function view(key,{auto=false,animate=true}={}){if(auto&&!draws.has(key)&&roster.length)spin(key);const d=draws.get(key),age=d?Math.max(0,now()-d.start):0,spinning=Boolean(d&&age<SLOT_SPIN_SECONDS&&animate),reels=d?slotReels(d.student.suffix,animate?age:SLOT_SPIN_SECONDS):null,pull=age<.24?1-Math.pow(1-age/.24,2):age<.78?Math.pow(1-(age-.24)/.54,2):0;return{digits:d?(spinning?reels.map(r=>r.digit).join(''):d.student.suffix):'--',reels,name:d&&!spinning?d.student.name:'',spinning,leverPull:d&&spinning?pull:0,key:revision+':'+(spinning?Math.floor(age*60):'done'),count:roster.length,remaining:remaining().length,error};}
 async function chooseFile(){const input=document.createElement('input');input.type='file';input.accept='.json,.csv,.tsv';input.hidden=true;document.body.append(input);return new Promise(resolve=>{input.onchange=async()=>{try{if(input.files[0])importRoster(await input.files[0].text());resolve(true);}catch(e){error=e.message;revision++;resolve(false);}finally{input.remove();}};input.oncancel=()=>{input.remove();resolve(false);};input.click();});}
 return{setCourse,importRoster,spin,view,chooseFile,get count(){return roster.length;},clear(){storage?.removeItem(storageKey(course));storage?.removeItem(usedKey());roster=[];used={};draws.clear();revision++;}};
}
export function drawStudentLottery(ctx,state,language='zh'){
 ctx.save();ctx.textAlign='center';ctx.textBaseline='alphabetic';
 const round=(x,y,w,h,r)=>{ctx.beginPath();ctx.roundRect(x,y,w,h,r);};
 const frame=ctx.createLinearGradient(0,210,0,372);frame.addColorStop(0,'#d8d9c5');frame.addColorStop(.12,'#748d88');frame.addColorStop(.45,'#a8bbb0');frame.addColorStop(1,'#4b6862');
 ctx.fillStyle='#0a1715';round(1132,210,274,162,17);ctx.fill();ctx.strokeStyle=frame;ctx.lineWidth=7;ctx.stroke();
 for(let i=0;i<2;i++){
  const x=1149+i*124,y=232,w=108,h=119;
  ctx.save();round(x,y,w,h,8);ctx.clip();ctx.fillStyle='#eff0df';ctx.fillRect(x,y,w,h);
  ctx.fillStyle='#203c36';ctx.font='76px '+SCREEN_MONO;
  if(state.reels){const pos=state.reels[i].position,whole=Math.floor(pos),fraction=pos-whole;for(let j=-1;j<=2;j++)ctx.fillText(String((whole+j+100)%10),x+w/2,318+(j-fraction)*93);}
  else ctx.fillText('—',x+w/2,318);
  const shade=ctx.createLinearGradient(0,y,0,y+h);shade.addColorStop(0,'#071e2899');shade.addColorStop(.22,'#071e2800');shade.addColorStop(.7,'#071e2800');shade.addColorStop(1,'#071e28a6');ctx.fillStyle=shade;ctx.fillRect(x,y,w,h);ctx.restore();
  ctx.strokeStyle='#d5e2d5';ctx.lineWidth=2;round(x,y,w,h,8);ctx.stroke();
 }
 // A mounted pull lever, with a short downward stroke and spring return.
 const pivot=[1438,320],angle=-Math.PI/2+(state.leverPull||0)*Math.PI*.91,knob=[pivot[0]+Math.cos(angle)*92,pivot[1]+Math.sin(angle)*92];
 ctx.fillStyle='#435f59';round(1412,301,48,39,9);ctx.fill();ctx.strokeStyle='#b9ccc6';ctx.lineWidth=10;ctx.lineCap='round';ctx.beginPath();ctx.moveTo(...pivot);ctx.lineTo(...knob);ctx.stroke();ctx.strokeStyle='#f0f0df';ctx.lineWidth=3;ctx.beginPath();ctx.moveTo(pivot[0]-2,pivot[1]);ctx.lineTo(knob[0]-2,knob[1]);ctx.stroke();
 const red=ctx.createRadialGradient(knob[0]-5,knob[1]-6,2,...knob,18);red.addColorStop(0,'#ffd3b1');red.addColorStop(.32,'#df6955');red.addColorStop(1,'#7d242a');ctx.fillStyle=red;ctx.beginPath();ctx.arc(...knob,17,0,Math.PI*2);ctx.fill();ctx.fillStyle='#d5dfce';ctx.beginPath();ctx.arc(...pivot,9,0,Math.PI*2);ctx.fill();
 ctx.font='30px '+SCREEN_FONT;ctx.fillStyle=state.error?'#ffada3':'#e3ece6';const text=state.error||state.name||(state.spinning?(language==='en'?'Drawing…':'摇号中…'):state.count?(state.remaining?(language==='en'?'Pull the lever':'拉动把手'):(language==='en'?'No candidates left':'本节候选已抽完')):(language==='en'?'Load local roster':'载入本机花名册'));ctx.fillText(text,1268,415,320);
 ctx.fillStyle='#91acb1';ctx.font='20px '+SCREEN_FONT;ctx.fillText(language==='en'?'Roster':'名单',...LOTTERY_ROSTER);ctx.restore();
}
export function lotteryHitTargets(T,boards,W,H,boardWidth,boardHeight){const targets=[];for(const [index,b]of boards.entries())for(const [action,[x,y],width,height]of [['board:lottery',LOTTERY_HANDLE,88,186],['board:roster',LOTTERY_ROSTER,110,35]]){const mesh=new T.Mesh(new T.PlaneGeometry(width/W*boardWidth,height/H*boardHeight),new T.MeshBasicMaterial({transparent:true,opacity:0,colorWrite:false,depthWrite:false}));mesh.position.set((x/W-.5)*boardWidth,(.5-y/H)*boardHeight,.018);mesh.userData={action,index,column:Math.floor(index/2)};mesh.visible=false;b.group.add(mesh);targets.push(mesh);}return targets;}
