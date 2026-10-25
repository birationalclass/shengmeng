// Local-only courses and offline packages never request a published roster.
export const COURSE_ROSTERS={'algebra-i':new URL('./assets/rosters/algebra-i.json',import.meta.url).href};
import {SCREEN_FONT} from './smart-screen-style.js';
export const LOTTERY_RECT=[1020,180,496,456],LOTTERY_HANDLE=[1445,290],LOTTERY_ROSTER=[1268,450];
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
export function createStudentLottery({storage=globalThis.localStorage,randomIndex=secureIndex,fetcher=globalThis.fetch,rosterSources=COURSE_ROSTERS,now=()=>performance.now()/1000,today=()=>new Date().toLocaleDateString('en-CA')}={}){
 let course='',lesson='',localOnly=globalThis.REFUGE_LOCAL===true,roster=[],used={},draws=new Map(),revision=0,error='',loading=false,request=0,controller=null,ready=Promise.resolve(false);const storageKey=id=>'refuge-roster-v1:'+id;
 const usedKey=()=> 'refuge-called-v1:'+course,lessonKey=()=>lesson+':'+today();
 function loadPublished(){
  const url=rosterSources[course];if(localOnly||globalThis.REFUGE_LOCAL===true||!url)return ready=Promise.resolve(false);const target=course,mine=++request;controller?.abort();controller=new AbortController();const activeController=controller;loading=true;error='';revision++;
  const timeout=setTimeout(()=>activeController.abort(),12000);
  ready=(async()=>{try{const response=await fetcher(url,{cache:'no-cache',signal:activeController.signal});if(!response.ok)throw Error('HTTP '+response.status);const rows=parseRoster(await response.text());if(mine!==request||course!==target||localOnly||globalThis.REFUGE_LOCAL===true)return false;roster=rows;try{storage?.setItem(storageKey(course),JSON.stringify(rows));}catch{}error='';draws.clear();revision++;return true;}catch(e){if(mine===request&&course===target&&!localOnly&&globalThis.REFUGE_LOCAL!==true){error=roster.length?'已使用缓存名单':'名单暂未取得 · 拉动把手重试';revision++;}return false;}finally{clearTimeout(timeout);if(mine===request){loading=false;revision++;}}})();return ready;
 }
 function setCourse(id,nextLesson=id,{localOnly:nextLocalOnly=false}={}){const policy=nextLocalOnly===true||globalThis.REFUGE_LOCAL===true;if(id!==course||policy!==localOnly){++request;controller?.abort();course=id;localOnly=policy;loading=false;error='';draws.clear();revision++;try{const saved=storage?.getItem(storageKey(id));roster=saved?parseRoster(saved):[];used=JSON.parse(storage?.getItem(usedKey())||'{}');}catch{roster=[];used={};}void loadPublished();}if(nextLesson!==lesson){lesson=nextLesson;draws.clear();revision++;}}
 function importRoster(text){const parsed=parseRoster(text);++request;controller?.abort();loading=false;storage?.setItem(storageKey(course),JSON.stringify(parsed));roster=parsed;used={};storage?.removeItem(usedKey());draws.clear();error='';revision++;return roster.length;}
 const remaining=()=>roster.filter(r=>!(used[lessonKey()]||[]).includes(r.key));
 function pick(){const candidates=remaining();if(!candidates.length)return null;const student=candidates[randomIndex(candidates.length)];(used[lessonKey()]??=[]).push(student.key);storage?.setItem(usedKey(),JSON.stringify(used));return student;}
 function spin(key){if(!roster.length)return false;const prior=draws.get(key);if(prior&&now()-prior.start<SLOT_SPIN_SECONDS)return false;const student=pick();if(!student)return false;draws.set(key,{student,start:now()});revision++;return true;}
 function view(key,{auto=false,animate=true}={}){if(auto&&!draws.has(key)&&roster.length)spin(key);const d=draws.get(key),age=d?Math.max(0,now()-d.start):0,spinning=Boolean(d&&age<SLOT_SPIN_SECONDS&&animate),reels=d?slotReels(d.student.suffix,animate?age:SLOT_SPIN_SECONDS):null,pull=age<.24?1-Math.pow(1-age/.24,2):age<.78?Math.pow(1-(age-.24)/.54,2):0;return{digits:d?(spinning?reels.map(r=>r.digit).join(''):d.student.suffix):'--',reels,name:d&&!spinning?d.student.name:'',spinning,leverPull:d&&spinning?pull:0,key:revision+':'+(spinning?Math.floor(age*60):'done'),count:roster.length,remaining:remaining().length,error,loading,source:!localOnly&&globalThis.REFUGE_LOCAL!==true&&rosterSources[course]?'github':'local'};}
 async function chooseFile(){if(!localOnly&&globalThis.REFUGE_LOCAL!==true&&rosterSources[course])return loadPublished();const input=document.createElement('input');input.type='file';input.accept='.json,.csv,.tsv';input.hidden=true;document.body.append(input);return new Promise(resolve=>{input.onchange=async()=>{try{if(input.files[0])importRoster(await input.files[0].text());resolve(true);}catch(e){error=e.message;revision++;resolve(false);}finally{input.remove();}};input.oncancel=()=>{input.remove();resolve(false);};input.click();});}
 return{setCourse,importRoster,spin,view,chooseFile,reload:loadPublished,get ready(){return ready;},get count(){return roster.length;},clear(){++request;controller?.abort();loading=false;storage?.removeItem(storageKey(course));storage?.removeItem(usedKey());roster=[];used={};draws.clear();revision++;}};
}
// Fixed paths and grain keep the chalk marks stable while the reels move.
const CHALK_DIGITS=[
 'M25 4 C3 3 3 65 24 66 C47 67 47 4 25 4 Z',
 'M13 17 L26 5 L25 65 M12 66 L38 66',
 'M7 16 C12 -1 41 0 42 18 C43 32 20 44 7 65 L43 65',
 'M8 10 C22 -1 43 4 41 19 C40 29 27 32 20 32 C47 30 49 66 24 67 C16 67 10 64 6 59',
 'M35 66 L36 4 L5 45 L46 45',
 'M42 5 L10 6 L8 31 C48 14 53 66 25 67 C17 67 10 64 6 59',
 'M39 7 C11 -6 -3 63 23 67 C48 71 51 27 26 29 C15 29 8 37 7 43',
 'M5 6 L44 5 C29 25 20 44 15 66',
 'M25 33 C-5 21 8 2 25 4 C47 4 48 24 25 33 C-4 43 3 68 25 67 C52 67 52 44 25 33',
 'M41 29 C39 45 5 46 7 21 C9 -3 43 -2 42 26 C41 45 32 66 14 67'
];
function chalkStroke(ctx,path,color,width=3,seed=0){
 ctx.save();ctx.strokeStyle=color;ctx.lineWidth=width;ctx.lineCap='round';ctx.lineJoin='round';ctx.globalAlpha*=.84;
 ctx.setLineDash([11.7,.65,7.4,.45]);ctx.lineDashOffset=seed;ctx.stroke(path);
 ctx.translate(.55,-.4);ctx.globalAlpha*=.35;ctx.lineWidth=width*.48;ctx.setLineDash([2.5,2.1,4.2,1.2]);ctx.stroke(path);ctx.restore();
}
export function drawStudentLottery(ctx,state,language='zh'){
 ctx.save();ctx.textAlign='center';ctx.textBaseline='alphabetic';
 const round=(x,y,w,h,r)=>{ctx.beginPath();ctx.roundRect(x,y,w,h,r);};
 const ivory='#eee8c9',outline=new Path2D('M1152 211 C1225 209 1320 211 1384 210 Q1406 210 1405 232 L1406 350 Q1406 372 1384 371 L1153 372 Q1132 372 1133 350 L1132 233 Q1131 211 1152 211 Z');
 chalkStroke(ctx,outline,ivory,3.7,1);
 chalkStroke(ctx,new Path2D('M1156 221 C1220 219 1323 221 1382 220 Q1396 220 1395 235 L1396 348 Q1396 362 1382 361 L1157 362 Q1142 362 1143 348 L1142 236 Q1141 221 1156 221 Z'),ivory,2.5,4);
 for(let i=0;i<2;i++){
  const x=1149+i*124,y=232,w=108,h=119;
  ctx.save();round(x,y,w,h,9);ctx.clip();ctx.beginPath();ctx.rect(x,y+8,w,h-16);ctx.clip();
  const digit=(n,baseline)=>{ctx.save();ctx.translate(x+w/2-24,baseline-70);chalkStroke(ctx,new Path2D(CHALK_DIGITS[n]),ivory,3.6,i*3+n);ctx.restore();};
  if(state.reels){const pos=state.reels[i].position,whole=Math.floor(pos),fraction=pos-whole;for(let j=-1;j<=2;j++)digit((whole+j+100)%10,326+(j-fraction)*93);}
  else chalkStroke(ctx,new Path2D(`M${x+34} 291 Q${x+54} 290 ${x+74} 291`),ivory,3.8,i*3);
  ctx.restore();const window=new Path2D();window.roundRect(x,y,w,h,9);chalkStroke(ctx,window,ivory,2.6,i*4);
 }
 // The sketched lever uses the original pivot and hit area.
 const pivot=[1438,320],angle=-Math.PI/2+(state.leverPull||0)*Math.PI*.91,knob=[pivot[0]+Math.cos(angle)*92,pivot[1]+Math.sin(angle)*92];
 const mount=new Path2D();mount.roundRect(1412,301,48,39,7);chalkStroke(ctx,mount,ivory,2.5,5);
 const lever=new Path2D();lever.moveTo(...pivot);lever.lineTo(...knob);chalkStroke(ctx,lever,ivory,4.1,2);
 const ball=new Path2D();ball.arc(...knob,15.5,0,Math.PI*2);chalkStroke(ctx,ball,'#e2bb68',3.4,7);
 const hatch=new Path2D();for(let y=-11;y<=11;y+=4){const dx=Math.sqrt(13*13-y*y);hatch.moveTo(knob[0]-dx,knob[1]+y+2);hatch.lineTo(knob[0]+dx,knob[1]+y-2);}chalkStroke(ctx,hatch,'#e2bb68',1.6,3);
 const joint=new Path2D();joint.arc(...pivot,5,0,Math.PI*2);chalkStroke(ctx,joint,ivory,2.3,0);
 const showName=Boolean(state.name&&!state.error);ctx.font=(showName?'60px ':'30px ')+SCREEN_FONT;ctx.fillStyle=state.error?'#ffada3':'#e3ece6';const text=state.error||state.name||(state.loading&&!state.count?(language==='en'?'Loading course roster…':'读取课程花名册…'):state.spinning?(language==='en'?'Drawing…':'摇号中…'):state.count?(state.remaining?(language==='en'?'Pull the lever':'拉动把手'):(language==='en'?'No candidates left':'本节候选已抽完')):(language==='en'?'Load course roster':'载入课程花名册'));if(showName){
  const lines=[];let line='';for(const glyph of Array.from(text)){if(line&&ctx.measureText(line+glyph).width>480){lines.push(line);line=glyph;}else line+=glyph;}if(line)lines.push(line);
  lines.forEach((value,i)=>ctx.fillText(value,1268,438+i*60));
 }else ctx.fillText(text,1268,415,320);
 ctx.restore();
}
export function lotteryHitTargets(T,boards,W,H,boardWidth,boardHeight){const targets=[];for(const [index,b]of boards.entries())for(const [action,[x,y],width,height]of [['board:lottery',LOTTERY_HANDLE,88,186]]){const mesh=new T.Mesh(new T.PlaneGeometry(width/W*boardWidth,height/H*boardHeight),new T.MeshBasicMaterial({transparent:true,opacity:0,colorWrite:false,depthWrite:false}));mesh.position.set((x/W-.5)*boardWidth,(.5-y/H)*boardHeight,.018);mesh.userData={action,index,column:Math.floor(index/2)};mesh.visible=false;b.group.add(mesh);targets.push(mesh);}return targets;}
