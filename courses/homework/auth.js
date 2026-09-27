import {AUTH_API} from './auth-config.js';
const key='yuejian-auth-v1';
const root=document.createElement('div');root.id='homework-auth';
root.innerHTML=`<button class="auth-entry" type="button" aria-haspopup="dialog"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" aria-hidden="true"><circle cx="12" cy="8" r="3.5"/><path d="M4.5 21v-2.5a7.5 7.5 0 0 1 15 0V21"/></svg><span>登录 / 注册</span></button>
<dialog class="auth-dialog" aria-labelledby="auth-title"><button class="auth-close" type="button" aria-label="关闭登录窗口">×</button><p class="auth-kicker">阅见 · HOMEWORK</p><h1 id="auth-title">欢迎回来</h1><p class="auth-intro">用邮箱地址和个人密码登录。</p>
<div class="auth-tabs" role="group" aria-label="账号操作"><button type="button" data-mode="login" aria-pressed="true">登录</button><button type="button" data-mode="register" aria-pressed="false">首次注册</button></div>
<form id="auth-form"><label for="auth-id">邮箱地址</label><input id="auth-id" name="username" autocomplete="username" inputmode="email" maxlength="254" autocapitalize="none" spellcheck="false" placeholder="请输入邮箱地址" required aria-describedby="auth-email"><p id="auth-email" class="auth-hint">注册时验证学校邮箱。</p>
<div class="auth-verification" hidden><div class="auth-code-heading"><label for="auth-code">邮箱验证码</label><button id="auth-send" type="button">获取验证码</button></div><input id="auth-code" name="code" inputmode="numeric" autocomplete="one-time-code" pattern="[0-9]{6}" maxlength="6" placeholder="邮件中的 6 位数字"><p class="auth-hint">10 分钟内有效。<a href="https://mail.stu.ecnu.edu.cn" target="_blank" rel="noopener">打开学校邮箱 ↗</a></p></div>
<label for="auth-password" id="auth-password-label">个人密码</label><div class="auth-password-row"><input id="auth-password" name="password" type="password" autocomplete="current-password" minlength="10" maxlength="128" placeholder="至少 10 个字符" required><button id="auth-show" type="button" aria-label="显示密码" aria-pressed="false">显示</button></div>
<div class="auth-confirm" hidden><label for="auth-confirm">再次输入密码</label><input id="auth-confirm" type="password" autocomplete="new-password" minlength="10" maxlength="128" placeholder="再次输入新密码"></div>
<div class="auth-options"><label><input id="auth-remember" type="checkbox">在此设备记住我 30 天</label><button type="button" data-mode="reset">忘记密码</button></div>
<button class="auth-primary" id="auth-submit" type="submit">登录</button></form>
<section class="auth-profile" hidden><p class="auth-profile-id"></p><p class="auth-profile-email"></p><p class="auth-profile-role"></p><button class="auth-primary" id="auth-continue" type="button">返回作业本</button><div class="auth-profile-actions"><button type="button" data-mode="reset">重设密码</button><button type="button" id="auth-logout">退出登录</button></div></section>
<p class="auth-status" role="status" aria-live="polite"></p><p class="auth-footnote">登录后查看个人作业；未登录页面仅供体验。</p></dialog>`;
document.body.append(root);
const entry=root.querySelector('.auth-entry');
function mountAccount(){const slot=document.querySelector('#account-slot');const parent=slot&&root.dataset.signedIn!=='true'?slot:root;if(entry.parentElement!==parent)parent.append(entry);}
window.addEventListener('homework-tools-ready',mountAccount);
const $=s=>root.querySelector(s),$$=s=>[...root.querySelectorAll(s)];
const dialog=$('dialog'),form=$('form');
let mode='login',session=null,user=null,busy=false,challenge=null,retryAt=0,lastFocus=null;
function message(text,error=false){$('.auth-status').textContent=text;$('.auth-status').classList.toggle('is-error',error);}
function load(){try{return JSON.parse(localStorage.getItem(key)||sessionStorage.getItem(key)||'null');}catch{return null;}}
function clear(){session=null;user=null;for(const storage of [localStorage,sessionStorage])try{storage.removeItem(key);}catch{}updateEntry();}
function save(data,remember){
 clear();session={token:data.token,expiresAt:data.expiresAt};user=data.user;
 try{(remember?localStorage:sessionStorage).setItem(key,JSON.stringify(session));}catch{message('已登录；浏览器禁止保存登录状态，刷新后需重新登录。');}
 updateEntry();
}
async function call(path,input,token=session?.token){
 let response;
 try{response=await fetch(AUTH_API+path,{method:input===undefined?'GET':'POST',headers:{...(input===undefined?{}:{'Content-Type':'application/json'}),...(token?{Authorization:'Bearer '+token}:{})},body:input===undefined?undefined:JSON.stringify(input),cache:'no-store',credentials:'omit',signal:AbortSignal.timeout(25000)});}
 catch{throw new Error('无法连接登录服务，请检查网络后重试。');}
 let data;try{data=await response.json();}catch{throw new Error('登录服务响应异常，请稍后重试。');}
 if(token&&session?.token!==token)throw new Error('账号状态已改变，请重新打开作业。');
 if(!response.ok)throw Object.assign(new Error(data.error||'操作失败，请稍后重试。'),{status:response.status,retryAfter:Number(response.headers.get('Retry-After'))||0});
 return data;
}
function updateEntry(){
 entry.querySelector('span').textContent=user?(user.role==='teacher'?'教师 · ':'')+user.studentId:'登录 / 注册';
 entry.setAttribute('aria-label',user?'账号：'+user.studentId:'登录或注册');
 root.dataset.signedIn=String(Boolean(user));
 mountAccount();
 window.dispatchEvent(new CustomEvent('homework-auth-change',{detail:user}));
}
function address(){const id=$('#auth-id').value.trim().toLowerCase();return /^\d{11}$/.test(id)?id+'@stu.ecnu.edu.cn':/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(id)?id:'';}
// Keep existing account IDs compatible; identity and permissions remain server-validated.
function accountId(){return address().replace(/^(\d{11})@stu\.ecnu\.edu\.cn$/,'$1');}
function updateAddress(){$('#auth-email').textContent=address()?(mode==='login'?'账号邮箱：':'验证码将发送到 ')+address():'输入完整邮箱；学号自动补全 @stu.ecnu.edu.cn';}
function resetSecrets(){challenge=null;$('#auth-code').value='';$('#auth-password').value='';$('#auth-confirm').value='';$('#auth-password').type='password';$('#auth-show').textContent='显示';$('#auth-show').setAttribute('aria-pressed','false');}
function setMode(next){
 if(busy)return;mode=next;resetSecrets();message('');
 const profile=next==='profile',verification=['register','reset'].includes(next);
 form.hidden=profile;$('.auth-profile').hidden=!profile;$('.auth-tabs').hidden=profile;
 $('#auth-title').textContent={login:'欢迎回来',register:'开启你的作业本',reset:'重设个人密码',profile:'已登录'}[next];
 $('.auth-intro').textContent={login:'用邮箱地址和个人密码登录。',register:'验证学校邮箱，再设置个人密码。',reset:'验证学校邮箱，为账号设置新密码。',profile:'账号已通过服务器验证。'}[next];
 $('.auth-verification').hidden=!verification;$('.auth-confirm').hidden=!verification;
 $('#auth-code').required=verification;$('#auth-code').disabled=!verification;$('#auth-confirm').required=verification;$('#auth-confirm').disabled=!verification;
 $('#auth-password').autocomplete=verification?'new-password':'current-password';$('#auth-password-label').textContent=verification?'设置个人密码':'个人密码';
 $('#auth-submit').textContent={login:'登录',register:'验证并注册',reset:'验证并更新密码'}[next]||'登录';
 $$('.auth-tabs button').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.mode===next)));
 $('.auth-options [data-mode=reset]').hidden=verification;
 if(profile&&user){$('.auth-profile-id').textContent=user.studentId;$('.auth-profile-email').textContent=user.email;$('.auth-profile-role').textContent=user.role==='teacher'?'教师账号':'学生账号';}
 updateAddress();refreshSend();
}
function refreshSend(){const seconds=Math.max(0,Math.ceil((retryAt-Date.now())/1000));$('#auth-send').disabled=busy||seconds>0;$('#auth-send').textContent=seconds?seconds+' 秒后可重发':challenge?'重新发送':'获取验证码';}
function setBusy(value){busy=value;form.setAttribute('aria-busy',String(value));$$('form input,form button,.auth-tabs button,.auth-profile-actions button').forEach(el=>el.disabled=value);if(!value){const verification=['register','reset'].includes(mode);$('#auth-code').disabled=!verification;$('#auth-confirm').disabled=!verification;}refreshSend();}
function open(){lastFocus=document.activeElement;setMode(user?'profile':'login');dialog.showModal();(user?$('#auth-continue'):$('#auth-id')).focus();}
entry.onclick=open;
$('.auth-close').onclick=()=>dialog.close();$('#auth-continue').onclick=()=>dialog.close();
dialog.addEventListener('close',()=>{if(!busy)resetSecrets();lastFocus?.focus();});
dialog.addEventListener('keydown',event=>event.stopPropagation());
$$('[data-mode]').forEach(b=>b.onclick=()=>{if(user)$('#auth-id').value=user.email;setMode(b.dataset.mode);});
$('#auth-id').onblur=()=>{const id=$('#auth-id').value.trim();if(/^\d{11}$/.test(id))$('#auth-id').value=id+'@stu.ecnu.edu.cn';updateAddress();};
$('#auth-id').oninput=()=>{challenge=null;$('#auth-code').value='';updateAddress();refreshSend();};
$('#auth-show').onclick=()=>{const visible=$('#auth-password').type==='password';$('#auth-password').type=visible?'text':'password';$('#auth-show').textContent=visible?'隐藏':'显示';$('#auth-show').setAttribute('aria-pressed',String(visible));$('#auth-show').setAttribute('aria-label',visible?'隐藏密码':'显示密码');};
$('#auth-send').onclick=async()=>{
 if(busy)return;if(!address()){message('请输入完整邮箱或 11 位学号。',true);$('#auth-id').focus();return;}
 setBusy(true);message('正在发送验证码…');
 try{const data=await call('/api/request-code',{studentId:accountId(),purpose:mode==='reset'?'reset':'register'});challenge=data.challengeId;retryAt=Date.now()+data.retryAfter*1000;message('验证码已发送到 '+data.email+'，请检查收件箱和垃圾邮件。');}
 catch(error){if(error.retryAfter)retryAt=Date.now()+error.retryAfter*1000;message(error.message,true);}
 finally{setBusy(false);if(challenge&&dialog.open)$('#auth-code').focus();}
};
form.onsubmit=async event=>{
 event.preventDefault();if(busy)return;
 if(!address()){message('请输入完整邮箱或 11 位学号。',true);return;}
 const verification=mode!=='login',remember=$('#auth-remember').checked;
 if(verification&&!challenge){message('请先获取邮箱验证码。',true);return;}
 if(verification&&$('#auth-password').value!==$('#auth-confirm').value){message('两次输入的密码不一致。',true);$('#auth-confirm').focus();return;}
 const input={studentId:accountId(),password:$('#auth-password').value,remember};
 if(verification)Object.assign(input,{challengeId:challenge,code:$('#auth-code').value});
 const path={login:'/api/login',register:'/api/register',reset:'/api/reset-password'}[mode];
 setBusy(true);message('正在验证…');
 try{const data=await call(path,input);setBusy(false);save(data,remember);setMode('profile');message('登录成功。');$('#auth-continue').focus();}
 catch(error){message(error.message,true);}finally{setBusy(false);}
};
$('#auth-logout').onclick=async()=>{
 if(busy)return;setBusy(true);message('正在退出…');
 try{await call('/api/logout',{});clear();setBusy(false);setMode('login');message('已退出登录。');}
 catch(error){message(error.message,true);}finally{setBusy(false);}
};
let restoring=null;
async function restore(){
 if(restoring||busy)return;const saved=load();
 if(!saved?.token||saved.expiresAt<=Date.now()){if(session)clear();return;}
 session=saved;
 restoring=call('/api/session',undefined,saved.token).then(data=>{if(session?.token!==saved.token)return;user=data.user;updateEntry();}).catch(error=>{if(error.status===401){clear();if(dialog.open){setMode('login');message('登录已过期，请重新登录。',true);}}else if(dialog.open)message(error.message,true);}).finally(()=>{restoring=null;});
 await restoring;
}
setInterval(()=>{if(dialog.open)refreshSend();if(session&&session.expiresAt<=Date.now()){clear();if(dialog.open){setMode('login');message('登录已过期，请重新登录。',true);}}},1000);
window.addEventListener('storage',event=>{if(event.key===key){session=null;user=null;updateEntry();restore();}});
window.addEventListener('focus',()=>restore());
export const authRequest=call;
export const currentUser=()=>user;
export const openAccount=open;
updateEntry();restore();
