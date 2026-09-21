import {RECORDS_CONFIG} from './records-config.mjs?v=records5-compact';
import {createRecordsApi} from './records-api.mjs?v=records5-compact';
export function createCompletionRecords({getCampaign,t,storage,onLogin,onOpen=()=>{}}){
 const $=id=>document.getElementById(id),login=$('playerDialog'),history=$('recordsDialog'),id=$('playerStudentId');
 const api=createRecordsApi({config:RECORDS_CONFIG,t});
 let account,sessionToken='',lookupToken='',lookupId='',lookupRun=0,lookupAbort,entering=false,startResolve;
 let pending=null,saving=false,retryTimer,adminToken='',rows=[],recordsRun=0,refreshTimer,saveMessage='';
 const read=key=>{try{return JSON.parse(storage?.getItem(key)||'null');}catch{return null;}};
 const write=(key,value)=>{try{storage?.setItem(key,JSON.stringify(value));}catch{}};
 const pendingKey=()=>`group-sudoku-pending:${account?.id}`;
 const displayName=()=>account?.kind==='guest'?t('游客 ','Guest ')+account.name:account?.name||'';
 const text=(key,zh,en)=>$(key).textContent=t(zh,en);
 function mobileHeight(){const v=window.visualViewport;document.documentElement.style.setProperty('--records-viewport-height',(v?.height||innerHeight)+'px');document.documentElement.style.setProperty('--records-viewport-top',(v?.offsetTop||0)+'px');}
 window.visualViewport?.addEventListener('resize',mobileHeight);window.visualViewport?.addEventListener('scroll',mobileHeight);mobileHeight();
 function sync(){
  text('recordsToggle','通关记录','Records');text('playerTitle','开启八域之旅','Enter the eight domains');text('playerIntro','选择身份，通关进度自动保存。','Choose how to enter. Completed levels are saved automatically.');
  text('studentLogin','学号登录','Student login');text('guestLogin','游客登录','Guest login');text('playerIdLabel','学号','Student ID');text('playerIdHint','输入完整的 11 位学号，自动核对姓名。','Enter your 11-digit student ID to find your name.');
  id.placeholder=t('轻点输入学号','Tap to enter student ID');text('playerEnter','确认姓名并进入','Confirm name and enter');text('playerBack','返回','Back');text('playerRetry','重新查询','Retry lookup');
  text('playerGuestNote','游客将以“游客＋编号”显示在通关记录中。','Guests appear in the records with a Guest prefix and an assigned code.');
  $('playerIdentity').textContent=account?t('当前身份：','Playing as: ')+displayName():'';text('playerChange','切换登录','Switch player');
  text('recordsTitle','通关记录','Completion records');text('recordsIntro','最高通关关卡优先；同关卡按通关时间从早到晚排列。姓名显示拼音首字母。','Highest completed level first; ties are ordered by the time reached, earliest first. Student names use pinyin initials.');
  text('recordsRefresh','刷新','Refresh');text('recordsSync','重试同步','Retry sync');$('recordsSync').hidden=!pending;$('recordsSync').disabled=saving;
  text('recordsTeacherSummary','教师导出完整记录','Teacher export');text('recordsPasswordLabel','教师口令','Teacher password');text('recordsTeacherLogin','登录','Sign in');text('recordsExport','导出 CSV','Export CSV');text('recordsLogout','退出教师查看','Sign out');text('recordsClose','关闭','Close');
  $('playerSaveStatus').textContent=saveMessage;
 }
 function invalidate(){lookupRun++;lookupAbort?.abort();lookupToken='';lookupId='';$('playerName').textContent='';$('playerEnter').disabled=true;$('playerLoginStatus').textContent='';}
 async function lookup(){
  if(entering)return;id.value=id.value.replace(/\D/g,'').slice(0,11);invalidate();$('playerRetry').hidden=true;if(id.value.length!==11)return;
  const run=lookupRun,sid=id.value;lookupAbort=new AbortController();text('playerLoginStatus','正在核对姓名…','Checking your name…');
  try{const data=await api('/api/lookup',{method:'POST',body:{studentId:sid},signal:lookupAbort.signal});if(run!==lookupRun)return;lookupToken=data.lookupToken;lookupId=sid;$('playerName').textContent=data.name;$('playerEnter').disabled=false;text('playerLoginStatus','请核对姓名，再进入游戏。','Confirm your name before entering.');}
  catch(e){if(run!==lookupRun)return;$('playerLoginStatus').textContent=e.message;$('playerRetry').hidden=false;}
 }
 function enableLogin(enabled){entering=!enabled;for(const key of ['studentLogin','guestLogin','playerBack'])$(key).disabled=!enabled;id.readOnly=!enabled;$('playerEnter').disabled=!enabled||!lookupToken;}
 async function enter(mode){
  if(entering||mode==='student'&&(!lookupToken||lookupId!==id.value))return;
  enableLogin(false);text('playerLoginStatus','正在进入…','Entering…');text('playerChoiceStatus','正在连接服务器…','Connecting…');
  try{
   const guest=read('group-sudoku-guest-session');
   const data=await api('/api/login',{method:'POST',body:mode==='student'?{mode,studentId:lookupId,lookupToken}:{mode,sessionToken:guest?.sessionToken}});
   account=data.account;sessionToken=data.sessionToken;
   if(mode==='guest')write('group-sudoku-guest-session',{sessionToken,account});else write('group-sudoku-last-student',account.id);
   await onLogin(data);pending=read(pendingKey());login.close();enableLogin(true);saveMessage='';sync();startResolve?.(data);startResolve=null;
   if(pending)flush();else if(getCampaign().completed.length>(data.record?.completedLevels||0))queueProgress();
  }catch(e){enableLogin(true);$('playerLoginStatus').textContent=e.message;$('playerChoiceStatus').textContent=e.message;}
 }
 $('studentLogin').onclick=()=>{$('playerChoices').hidden=true;$('playerStudentForm').hidden=false;invalidate();const last=read('group-sudoku-last-student');if(typeof last==='string')id.value=last;id.focus({preventScroll:true});if(id.value.length===11)lookup();};
 $('guestLogin').onclick=()=>enter('guest');$('playerBack').onclick=()=>{invalidate();$('playerStudentForm').hidden=true;$('playerChoices').hidden=false;$('studentLogin').focus();};
 id.addEventListener('input',lookup);$('playerRetry').onclick=lookup;$('playerStudentForm').onsubmit=e=>{e.preventDefault();enter('student');};
 login.addEventListener('cancel',e=>e.preventDefault());$('playerChange').onclick=()=>location.reload();
 function queueProgress(){
  if(!account||!getCampaign().completed.length)return;
  const boards=structuredClone(getCampaign().finished),count=Object.keys(boards).length;
  if(!pending||Object.keys(pending.boards).length<count){pending={boards,submissionId:crypto.randomUUID()};write(pendingKey(),pending);}
  flush();
 }
 async function flush(){
  if(saving||!pending||!account)return;clearTimeout(retryTimer);saving=true;const current=pending;saveMessage=t('正在自动保存通关进度…','Saving completed levels…');sync();
  try{
   const data=await api('/api/progress',{method:'POST',token:sessionToken,body:current});if(!data.saved)throw Error(t('服务器未确认保存。','Save was not confirmed.'));
   if(pending.submissionId===current.submissionId){pending=null;write(pendingKey(),null);}
   saveMessage=t(`已自动保存 · ${data.record.completedLevels} / 8 关`,`Saved · ${data.record.completedLevels} / 8 levels`);if(history.open)loadRecords();
  }catch(e){saveMessage=t('进度已留在本机，等待同步。','Progress kept on this device; waiting to sync.');if(e.status===401)saveMessage=t('登录已过期，请在设置中重新登录；本机进度已保留。','Session expired. Sign in again in Settings; local progress is safe.');else retryTimer=setTimeout(flush,15000);}
  finally{saving=false;sync();if(pending&&pending!==current)flush();}
 }
 window.addEventListener('online',flush);document.addEventListener('visibilitychange',()=>{if(!document.hidden)flush();});$('recordsSync').onclick=flush;
 function displayRecords(records){
  rows=records;const list=$('recordsList');list.replaceChildren();if(!records.length){const p=document.createElement('p');p.className='records-empty';p.textContent=t('暂无通关记录。','No completed levels yet.');list.append(p);return;}
  records.forEach((r,index)=>{
   const card=document.createElement('article');card.className='completion-card';
   const top=document.createElement('div');top.className='record-main';
   const h=document.createElement('h3');h.textContent=`${index+1}. ${r.kind==='guest'&&document.documentElement.lang==='en'?r.name.replace(/^游客 /,'Guest '):r.name}`;h.title=h.textContent;
   const level=r.highestLevel||9,progress=document.createElement('span');progress.className='record-level';progress.textContent=`${level}×${level} · ${r.completedLevels}/8`;progress.setAttribute('aria-label',t(`最高通关 ${level}×${level}，已通关 ${r.completedLevels} 关`,`Highest ${level}×${level}, ${r.completedLevels} levels completed`));
   top.append(h,progress);
   const meta=document.createElement('div');meta.className='record-meta';
   const sid=document.createElement('span');sid.textContent=r.studentId||'';
   const date=document.createElement('time'),iso=r.reachedAt||r.firstCompletedAt;date.dateTime=iso;
   const parts=new Intl.DateTimeFormat('en-GB',{timeZone:'Asia/Shanghai',year:'numeric',month:'2-digit',day:'2-digit',hour:'2-digit',minute:'2-digit',second:'2-digit',hourCycle:'h23'}).formatToParts(new Date(iso)),part=type=>parts.find(p=>p.type===type)?.value;
   date.textContent=`${part('year')}.${part('month')}.${part('day')} ${part('hour')}:${part('minute')}:${part('second')}`;
   date.title=t('达到最高关卡时间（北京时间）','Highest level reached (China Standard Time)');date.setAttribute('aria-label',date.title+' '+date.textContent);
   meta.append(sid,date);card.append(top,meta);list.append(card);
  });
 }
 async function loadRecords(){
  const run=++recordsRun; text('recordsStatus','正在读取服务器记录…','Loading records…');$('recordsRefresh').disabled=true;
  try{const data=await api(adminToken?'/api/admin/records':'/api/records',{token:adminToken});if(run!==recordsRun)return;displayRecords(data.records);text('recordsStatus',`已从服务器更新，共 ${data.records.length} 条。`,`Updated: ${data.records.length} record(s).`);}
  catch(e){if(run!==recordsRun)return;rows=[];$('recordsList').replaceChildren();$('recordsStatus').textContent=e.message;if(e.status===401){adminToken='';$('recordsAdminActions').hidden=true;}}
  finally{$('recordsRefresh').disabled=false;}
 }
 $('recordsToggle').onclick=()=>{onOpen();sync();history.showModal();mobileHeight();loadRecords();clearInterval(refreshTimer);refreshTimer=setInterval(()=>{if(history.open&&!document.hidden)loadRecords();},30000);};
 $('recordsRefresh').onclick=loadRecords;$('recordsClose').onclick=()=>history.close();
 $('recordsTeacherForm').onsubmit=async e=>{e.preventDefault();$('recordsTeacherLogin').disabled=true;try{const data=await api('/api/admin/session',{method:'POST',body:{password:$('recordsPassword').value}});$('recordsPassword').value='';adminToken=data.token;$('recordsAdminActions').hidden=false;await loadRecords();}catch(e){$('recordsStatus').textContent=e.message;}finally{$('recordsTeacherLogin').disabled=false;}};
 $('recordsLogout').onclick=()=>{adminToken='';$('recordsAdminActions').hidden=true;loadRecords();};
 history.addEventListener('close',()=>{clearInterval(refreshTimer);recordsRun++;rows=[];$('recordsList').replaceChildren();adminToken='';$('recordsAdminActions').hidden=true;$('recordsPassword').value='';});
 $('recordsExport').onclick=()=>{if(!adminToken)return;const quote=v=>'"'+String(v).replace(/^[=+@-]/,"'$&").replace(/"/g,'""')+'"';const csv='\ufeff'+[['排名','身份','学号','姓名','最高棋盘','已通关数','达到最高关卡时间（UTC）'],...rows.map((r,i)=>[i+1,r.kind==='guest'?'游客':'学生',r.studentId,r.name,r.highestLevel||9,r.completedLevels,r.reachedAt||r.firstCompletedAt])].map(r=>r.map(quote).join(',')).join('\r\n');const url=URL.createObjectURL(new Blob([csv],{type:'text/csv;charset=utf-8'})),a=document.createElement('a');a.href=url;a.download='群数独-通关记录.csv';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);};
 for(const modal of [login,history])modal.addEventListener('keydown',e=>e.stopPropagation());window.addEventListener('course-language',()=>{sync();if(history.open)displayRecords(rows);});sync();
 return {sync,completed:queueProgress,start(){onOpen();sync();login.showModal();mobileHeight();return new Promise(resolve=>startResolve=resolve);}};
}
