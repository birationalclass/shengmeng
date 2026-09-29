import {GALAXIES} from './galaxy-campaign.mjs?v=nebula-69';
import {createConnection} from '../../../visuals/group-sudoku/connection.mjs?v=background1';
import {createEndlessMusic} from './endless-music.mjs?v=nebula-70';

export function mountCosmicControls({t,api,read,write,getAccount,assign,getProgress,clearJourney,render,onSession=()=>{}}){
 const $=id=>document.getElementById(id),svg=p=>`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${p}</svg>`;
 const records=document.createElement('button');records.id='cosmicRecords';records.innerHTML=svg('<path d="M12 5C8 3 5 3 3 4v15c3-1 6-1 9 1 3-2 6-2 9-1V4c-3-1-6-1-9 1Z"/><path d="M12 5v15"/>');$('cosmicLang').before(records);
 const motion=document.createElement('button');motion.id='cosmicPause';motion.innerHTML=svg('<path d="M8 5v14M16 5v14"/>');records.before(motion);
 $('cosmicStudentForm').insertAdjacentHTML('beforeend','<button type="button" id="identityRetry" hidden></button><button type="button" id="identityBack"></button><button type="button" id="identityOffline"></button>');
 $('identityText').insertAdjacentHTML('afterend','<p id="identityServer" role="status"></p>');
 $('prefsStudent').insertAdjacentHTML('afterend','<p id="prefsServer" role="status"></p>');
 $('cosmicPreferences').insertAdjacentHTML('beforeend',`<section class="music-settings"><h3 id="musicTitle"></h3><label class="cosmic-setting"><span id="musicToggleLabel"></span><input id="musicEnabled" type="checkbox"></label><div class="volume-heading"><label for="musicVolume" id="musicVolumeLabel"></label><output id="musicVolumeValue"></output></div><input id="musicVolume" type="range" min="0" max="100" value="12"><p id="musicStatus"></p></section><button id="clearCosmicData"></button>`);
 document.body.insertAdjacentHTML('beforeend',`<audio id="backgroundMusic"></audio><dialog id="cosmicRecordPanel" class="cosmic-dialog"><button class="cosmic-close" id="closeCosmicRecords">×</button><h2 id="cosmicRecordsTitle"></h2><div class="record-toolbar"><button id="refreshCosmicRecords"></button><span id="cosmicRecordsStatus" role="status"></span></div><div id="cosmicRecordRows"></div><p id="cosmicRecordsNote"></p></dialog><dialog id="cosmicClearDialog" class="cosmic-dialog"><h2 id="cosmicClearTitle"></h2><p id="cosmicClearNote"></p><div class="dialog-actions"><button id="cancelCosmicClear"></button><button id="confirmCosmicClear"></button></div></dialog>`);
 let server='connecting',desired={mode:'guest',sessionToken:read('group-sudoku-guest-session')?.sessionToken},verified=false,lookupToken='',lookupId='',run=0,abort;
 const invalidate=()=>{run++;abort?.abort();lookupToken='';lookupId='';$('confirmIdentity').disabled=true;$('cosmicStudentName').textContent='';$('cosmicLoginStatus').textContent='';};
 const connection=createConnection({run:async({signal})=>{
  if(verified)return;
  const body={...desired};if(body.mode==='student'&&!body.lookupToken){const found=await api('/api/lookup',{method:'POST',body:{studentId:body.studentId},signal});body.lookupToken=found.lookupToken;}
  const data=await api('/api/login',{method:'POST',body,signal});if(signal.aborted)return;
  // Identity is shared with Sudoku; this module never uploads simulated records.
  const before=getAccount(),journey=getProgress();assign(data.account);if(before.id!==data.account.id&&journey>getProgress()){write('generators-galaxy-demo:'+data.account.id,journey);assign(data.account);}
  if(data.account.kind==='guest'){write('group-sudoku-guest-session',{sessionToken:data.sessionToken,account:data.account});desired.sessionToken=data.sessionToken;}
  onSession({...data,previousAccount:before});verified=true;
 },onState:state=>{server=state;sync();}});
 async function lookup(){
  const input=$('cosmicStudentId');input.value=input.value.replace(/\D/g,'').slice(0,11);invalidate();$('identityRetry').hidden=true;if(input.value.length!==11)return;
  const own=run;abort=new AbortController();$('cosmicLoginStatus').textContent=t('正在核对姓名…','Checking your name…');
  try{const data=await api('/api/lookup',{method:'POST',body:{studentId:input.value},signal:abort.signal});if(own!==run)return;lookupToken=data.lookupToken;lookupId=input.value;$('cosmicStudentName').textContent=data.name;$('confirmIdentity').disabled=false;$('cosmicLoginStatus').textContent=t('请核对姓名，再进入。','Confirm your name before entering.');}
  catch(error){if(own!==run)return;$('cosmicLoginStatus').textContent=error.message;$('identityRetry').hidden=false;}
 }
 function enter(mode){
  if(mode==='student'&&(!lookupToken||lookupId!==$('cosmicStudentId').value))return;
  connection.pause();verified=false;
  if(mode==='student'){desired={mode,studentId:lookupId,lookupToken};assign({id:lookupId,kind:'student',name:$('cosmicStudentName').textContent});write('group-sudoku-last-student',lookupId);}
  else {const shared=read('group-sudoku-guest-session');desired={mode:'guest',sessionToken:shared?.sessionToken};assign(shared?.account||read('group-sudoku-local-guest'));}
  $('cosmicLogin').close();connection.wake();sync();
 }
 $('studentIdentity').onclick=()=>{invalidate();$('identityChoices').hidden=true;$('cosmicStudentForm').hidden=false;const last=read('group-sudoku-last-student');if(typeof last==='string')$('cosmicStudentId').value=last;$('cosmicStudentId').focus();if($('cosmicStudentId').value.length===11)lookup();};
 $('cosmicStudentId').oninput=lookup;$('identityRetry').onclick=lookup;
 $('identityBack').onclick=()=>{invalidate();$('cosmicStudentForm').hidden=true;$('identityChoices').hidden=false;};
 $('guestIdentity').onclick=$('identityOffline').onclick=()=>enter('guest');
 $('cosmicStudentForm').onsubmit=e=>{e.preventDefault();enter('student');};
 $('cosmicLogin').addEventListener('close',()=>{invalidate();$('identityChoices').hidden=false;});
 for(const event of ['online','offline','pageshow'])window.addEventListener(event,()=>connection.wake());document.addEventListener('visibilitychange',()=>connection.wake());
 records.onclick=()=>{sync();$('cosmicRecordPanel').showModal();};$('closeCosmicRecords').onclick=()=>$('cosmicRecordPanel').close();$('refreshCosmicRecords').onclick=()=>{sync();$('cosmicRecordsStatus').textContent=t('已从本机更新','Updated from this device');};
 $('resetDemo').onclick=$('clearCosmicData').onclick=()=>$('cosmicClearDialog').showModal();
 $('cancelCosmicClear').onclick=()=>$('cosmicClearDialog').close();$('confirmCosmicClear').onclick=()=>{clearJourney();$('cosmicMotion').checked=true;$('cosmicMotion').dispatchEvent(new Event('change'));$('cosmicClearDialog').close();$('cosmicPreferences').close();sync();};
 motion.onclick=()=>{$('cosmicMotion').checked=!$('cosmicMotion').checked;$('cosmicMotion').dispatchEvent(new Event('change'));sync();};
 function sync(){
  const text=(id,zh,en)=>$(id).textContent=t(zh,en),label=(id,zh,en)=>{const b=$(id),s=t(zh,en);b.setAttribute('aria-label',s);b.dataset.tip=s;};
  label('cosmicRecords','探索记录','Exploration records');label('cosmicPause',$('cosmicMotion').checked?'暂停星系动态':'继续星系动态',$('cosmicMotion').checked?'Pause scene':'Resume scene');motion.setAttribute('aria-pressed',String(!$('cosmicMotion').checked));motion.innerHTML=svg($('cosmicMotion').checked?'<path d="M8 5v14M16 5v14"/>':'<path d="m8 5 11 7-11 7Z"/>');
  const status=server==='connected'?t('身份服务器已连接','Identity server connected'):server==='offline'?t('当前离线 · 可继续探索','Offline · Continue exploring'):server==='retrying'?t('正在重连 · 可继续探索','Reconnecting · Continue exploring'):t('后台连接中 · 可直接进入','Connecting in background · Ready to enter');$('identityServer').textContent=$('prefsServer').textContent=status;
  document.querySelector('.cosmic-home').setAttribute('aria-label',t('返回代数学','Back to algebra'));const a=getAccount();$('prefsStudent').textContent=a.kind==='student'?`${a.name} · ${a.id}`:a.local?t('游客（本机）','Guest (this device)'):t('游客 ','Guest ')+a.name;
  text('identityRetry','重新查询','Retry lookup');text('identityBack','返回','Back');text('identityOffline','先以游客身份游玩','Play as guest for now');text('guestIdentity','游客进入 · 无需等待','Enter as guest · No waiting');
  text('clearCosmicData','清除本地记录','Clear local data');text('cosmicClearTitle','清除本机模拟航程？','Clear this device’s demo journey?');text('cosmicClearNote','仅清除当前身份的星系模拟进度与星云设置，群数独记录和登录身份保留。','Clears this identity’s local galaxy demo and nebula settings. Sudoku records and identity are retained.');text('cancelCosmicClear','取消','Cancel');text('confirmCosmicClear','确认清除','Clear');
  text('cosmicRecordsTitle','探索记录','Exploration records');text('refreshCosmicRecords','刷新','Refresh');text('cosmicRecordsNote','通关条件尚未启用；这里仅显示本机模拟航程，不计入正式成绩。','Win conditions are not enabled. This is local simulated progress, not official results.');
  $('cosmicRecordRows').replaceChildren(...GALAXIES.map((g,i)=>{const row=document.createElement('div');row.className='cosmic-record-row';const name=document.createElement('span'),state=document.createElement('small');name.textContent=String(i+1).padStart(2,'0')+' · '+g.name;state.textContent=i<getProgress()?t('已模拟探索','Simulated'):t('未完成','Not completed');row.append(name,state);return row;}));text('closeCosmicRecords','关闭','Close');
 }
 const music=createEndlessMusic({storage:localStorage,t});window.addEventListener('cosmic-ui-change',()=>{sync();music.sync();window.dispatchEvent(new Event('course-language'));});sync();
}
