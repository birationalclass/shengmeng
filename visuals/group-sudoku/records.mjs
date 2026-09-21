import {RECORDS_API_URL} from './records-config.mjs?v=records1';
export function createCompletionRecords({campaign,t,onOpen=()=>{}}){
 const $=id=>document.getElementById(id),dialog=$('completionDialog'),history=$('recordsDialog'),form=$('completionForm'),id=$('completionStudentId'),name=$('completionStudentName'),status=$('completionStatus'),submit=$('completionSubmit');
 let lookupToken='',lookupId='',lookupRun=0,lookupAbort,submissionId='',submitting=false,adminToken='',rows=[],recordsRun=0,refreshTimer;
 const text=(node,zh,en)=>node.textContent=t(zh,en);
 const ready=()=>campaign.completed.length===8;
 async function api(path,{method='GET',body,token,signal}={}){
  if(!RECORDS_API_URL)throw Error(t('通关登记服务尚未接通，请稍后再试。','The registration service is not connected yet. Please try again later.'));
  const response=await fetch(RECORDS_API_URL+path,{method,headers:{...(body?{'Content-Type':'application/json'}:{}),...(token?{Authorization:'Bearer '+token}:{})},...(body?{body:JSON.stringify(body)}:{}),signal:signal||AbortSignal.timeout(12000),cache:'no-store',credentials:'omit',referrerPolicy:'no-referrer'});
  const data=await response.json();if(!response.ok)throw Object.assign(Error(data.error||t('暂时无法连接，请稍后重试。','Unable to connect. Please try again.')),{status:response.status});return data;
 }
 function mobileHeight(){const v=window.visualViewport;document.documentElement.style.setProperty('--records-viewport-height',(v?.height||window.innerHeight)+'px');document.documentElement.style.setProperty('--records-viewport-top',(v?.offsetTop||0)+'px');}
 window.visualViewport?.addEventListener('resize',mobileHeight);window.visualViewport?.addEventListener('scroll',mobileHeight);mobileHeight();
 function sync(){
  text($('recordsToggle'),'通关记录','Records');text($('completionTitle'),'八域通关 · 登记成绩','Eight domains completed');text($('completionIntro'),'填写完整学号，确认点名册中的姓名后保存。','Enter your full student ID and confirm your roster name.');
  text($('completionIdLabel'),'学号','Student ID');text($('completionNameLabel'),'姓名','Name');text($('completionIdHint'),'请输入 11 位学号，将自动显示姓名。','Enter all 11 digits to find your name.');text($('completionNameHint'),'姓名由点名册自动匹配，请核对后提交。','Your name is matched from the class roster. Please check it before submitting.');
  id.placeholder=t('轻点输入学号','Tap to enter student ID');name.placeholder=t('输入学号后自动显示','Appears after entering your student ID');
  if(!submitting)text(submit,'确认姓名并保存','Confirm name and save');text($('completionLater'),'稍后登记','Register later');text($('completionClose'),'关闭','Close');
  text($('recordsTitle'),'通关记录','Completion records');text($('recordsIntro'),'全员可查看。姓名显示拼音首字母，学号部分隐藏。','Visible to everyone. Names use pinyin initials; student IDs are partially hidden.');text($('recordsRefresh'),'刷新','Refresh');text($('recordsRegister'),'登记本次通关','Register completion');$('recordsRegister').disabled=!ready();
  text($('recordsTeacherSummary'),'教师导出完整记录','Teacher export');text($('recordsPasswordLabel'),'教师口令','Teacher password');text($('recordsTeacherLogin'),'登录','Sign in');text($('recordsExport'),'导出 CSV','Export CSV');text($('recordsLogout'),'退出教师查看','Sign out');text($('recordsClose'),'关闭','Close');
 }
 function invalidate(){lookupRun++;lookupAbort?.abort();lookupToken='';lookupId='';name.value='';submit.disabled=true;submissionId='';$('completionSaved').hidden=true;submit.hidden=false;status.textContent='';}
 async function lookup(){
  if(submitting)return;const normalized=id.value.replace(/[^\d]/g,'').slice(0,11);if(normalized!==id.value)id.value=normalized;invalidate();
  if(id.value.length!==11)return;
  const current=lookupRun,sid=id.value;lookupAbort=new AbortController();const controller=lookupAbort,timer=setTimeout(()=>controller.abort(),12000);text(status,'正在核对姓名…','Checking your name…');
  try{const data=await api('/api/lookup',{method:'POST',body:{studentId:sid},signal:controller.signal});if(current!==lookupRun||sid!==id.value)return;name.value=data.name;lookupToken=data.lookupToken;lookupId=sid;submissionId=crypto.randomUUID();submit.disabled=!ready();text(status,'请核对上方姓名，再点击保存。','Check the name above, then save.');}
  catch(e){if(current!==lookupRun)return;status.textContent=e.name==='AbortError'?t('查询超时，请轻点“重新查询”。','Lookup timed out. Tap Retry.'):e.message;$('completionRetry').hidden=false;}
  finally{clearTimeout(timer);}
 }
 id.addEventListener('input',()=>{$('completionRetry').hidden=true;lookup();});id.addEventListener('compositionend',lookup);
 $('completionRetry').onclick=()=>{$('completionRetry').hidden=true;lookup();};
 function openRegistration(){
  if(!ready()){showRecords();return;}if(history.open)history.close();onOpen();sync();invalidate();$('completionRetry').hidden=true;if(!dialog.open)dialog.showModal();mobileHeight();id.focus({preventScroll:true});if(id.value.length===11)lookup();
 }
 function closeRegistration(){if(submitting)return;invalidate();dialog.close();}
 $('completionLater').onclick=closeRegistration;$('completionClose').onclick=closeRegistration;
 dialog.addEventListener('cancel',e=>{if(submitting)e.preventDefault();else invalidate();});
 form.addEventListener('submit',async e=>{
  e.preventDefault();if(submitting||!lookupToken||lookupId!==id.value||!ready())return;submitting=true;submit.disabled=true;id.readOnly=true;$('completionLater').disabled=true;$('completionClose').disabled=true;text(submit,'正在保存…','Saving…');text(status,'正在保存到服务器，请稍候。','Saving to the server…');
  try{
   const data=await api('/api/completions',{method:'POST',body:{studentId:lookupId,name:name.value,lookupToken,submissionId,boards:campaign.finished}});
   if(!data.saved)throw Error(t('服务器未确认保存，请重试。','The server did not confirm the save. Please retry.'));
   text(status,'已保存到服务器，所有同学都可在“通关记录”中查看。','Saved to the server. Everyone can view it in Completion records.');$('completionSaved').textContent=t('通关时间：','Completion time: ')+new Date(data.record.firstCompletedAt).toLocaleString(document.documentElement.lang,{timeZone:'Asia/Shanghai',hour12:false});$('completionSaved').hidden=false;submit.hidden=true;text($('completionLater'),'完成','Done');id.blur();
  }catch(e){status.textContent=e.message;if(e.status===401){lookupToken='';$('completionRetry').hidden=false;}else submit.disabled=false;}
  finally{submitting=false;id.readOnly=false;$('completionLater').disabled=false;$('completionClose').disabled=false;text(submit,'确认姓名并保存','Confirm name and save');}
 });
 function displayRecords(records){
  rows=records;const list=$('recordsList');list.replaceChildren();if(!records.length){const p=document.createElement('p');p.className='records-empty';p.textContent=t('暂无通关记录。','No completion records yet.');list.append(p);return;}
  for(const r of records){const card=document.createElement('article');card.className='completion-card';const h=document.createElement('h3');h.textContent=r.name;const student=document.createElement('p');student.textContent=r.studentId;const details=document.createElement('p');details.textContent=t('通关：','Completed: ')+new Date(r.firstCompletedAt).toLocaleString(document.documentElement.lang,{timeZone:'Asia/Shanghai',hour12:false});const date=document.createElement('p');date.textContent=t('更新：','Updated: ')+new Date(r.updatedAt).toLocaleString(document.documentElement.lang,{timeZone:'Asia/Shanghai',hour12:false});card.append(h,student,details,date);list.append(card);}
 }
 async function loadRecords(){
  const current=++recordsRun,feedback=$('recordsStatus');text(feedback,'正在读取服务器记录…','Loading server records…');$('recordsRefresh').disabled=true;
  try{
   const data=await api(adminToken?'/api/admin/records':'/api/records',{token:adminToken});if(current!==recordsRun)return;displayRecords(data.records);text(feedback,`已从服务器更新，共 ${data.records.length} 条。`,`Updated from the server: ${data.records.length} record(s).`);
  }catch(e){if(current!==recordsRun)return;displayRecords([]);feedback.textContent=e.message;if(e.status===401&&adminToken){adminToken='';$('recordsAdminActions').hidden=true;}}
  finally{$('recordsRefresh').disabled=false;}
 }
 function showRecords(){onOpen();sync();if(!history.open)history.showModal();mobileHeight();loadRecords();clearInterval(refreshTimer);refreshTimer=setInterval(()=>{if(history.open&&!document.hidden)loadRecords();},30000);}
 $('recordsToggle').onclick=showRecords;$('recordsRefresh').onclick=loadRecords;$('recordsClose').onclick=()=>history.close();$('recordsRegister').onclick=()=>{submit.hidden=false;openRegistration();};
 $('recordsTeacherForm').onsubmit=async e=>{e.preventDefault();const button=$('recordsTeacherLogin');button.disabled=true;try{const data=await api('/api/admin/session',{method:'POST',body:{password:$('recordsPassword').value}});$('recordsPassword').value='';adminToken=data.token;$('recordsAdminActions').hidden=false;await loadRecords();}catch(error){$('recordsStatus').textContent=error.message;}finally{button.disabled=false;}};
 $('recordsLogout').onclick=()=>{adminToken='';$('recordsAdminActions').hidden=true;loadRecords();};
 history.addEventListener('close',()=>{clearInterval(refreshTimer);recordsRun++;rows=[];$('recordsList').replaceChildren();adminToken='';$('recordsAdminActions').hidden=true;$('recordsPassword').value='';});
 $('recordsExport').onclick=()=>{
  if(!adminToken)return;const quote=v=>'"'+String(v).replace(/^[=+@-]/,"'$&").replace(/"/g,'""')+'"';const csv='\ufeff'+[['学号','姓名','首次通关时间（UTC）','更新时间（UTC）'],...rows.map(r=>[r.studentId,r.name,r.firstCompletedAt,r.updatedAt])].map(r=>r.map(quote).join(',')).join('\r\n');const url=URL.createObjectURL(new Blob([csv],{type:'text/csv;charset=utf-8'})),a=document.createElement('a');a.href=url;a.download='群数独-通关记录.csv';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
 };
 for(const modal of [dialog,history])modal.addEventListener('keydown',e=>e.stopPropagation());
 window.addEventListener('course-language',sync);sync();
 return {completed(){submit.hidden=false;openRegistration();},sync};
}
