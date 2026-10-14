import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';
const source=readFileSync(new URL('./social.js',import.meta.url),'utf8');
const probeCode=source.slice(source.indexOf('async function checkEntrySession('),source.indexOf('function message('));
function sessionSetup(){
 let timer,delay,now=0,resolve;const pending=new Promise(r=>resolve=r),nodes=new Map(),auth=[],users=[];
 const get=id=>{if(!nodes.has(id))nodes.set(id,{dataset:{entered:'false'},addEventListener(type,fn){this[type]=fn;},open:true});return nodes.get(id);};
 const ctx={AbortController,Promise,Error,performance:{now:()=>now},setTimeout(fn,ms){timer=fn;delay=ms;return 1;},clearTimeout(){timer=null;},$:get,entryLoginPending:false,entryLoginError:'',openAccount(){get('socialAuthStatus').textContent='';},request:()=>pending,setUser:user=>users.push(user),closeAccount(){},window:{refugeBoot:{auth:value=>auth.push(value)}}};
 const startup=source.slice(source.indexOf('let entryAuthTouched='),source.indexOf('// Pointer capture keeps'));
 const show=source.slice(source.indexOf('function showEntryLogin('),source.indexOf("window.addEventListener('refuge-preview-ready'"));
 vm.runInNewContext(probeCode+show+startup,ctx);return {get,auth,users,resolve,ctx,get delay(){return delay;},expire(){now=delay;timer?.();}};
}
const settle=async()=>{for(let i=0;i<12;i++)await Promise.resolve();};
test('a session server that never answers cannot retain checking state beyond its own deadline',async()=>{
 const s=sessionSetup();await settle();assert.equal(s.delay,2500);assert.deepEqual(s.auth,['pending']);
 s.expire();await settle();assert.equal(s.get('loading').dataset.sessionCheck,'timeout');assert.deepEqual(s.auth,['pending','anonymous']);assert.match(s.get('socialAuthStatus').textContent||s.ctx.entryLoginError,/超时/);
});
test('a late successful response cannot authenticate or overwrite the manual fallback after timeout',async()=>{
 const s=sessionSetup();await settle();s.expire();await settle();s.resolve({user:{name:'late'}});await settle();assert.deepEqual(s.auth,['pending','anonymous']);assert.deepEqual(s.users,[]);
});
test('typing in the login form cancels background checking and retains the manual flow',async()=>{
 const s=sessionSetup();await settle();s.get('socialName').value='typed';s.get('socialName').input();await settle();assert.equal(s.get('loading').dataset.sessionCheck,'manual');s.resolve({user:{name:'old-session'}});await settle();assert.deepEqual(s.users,[]);assert.equal(s.get('socialName').value,'typed');assert.deepEqual(s.auth,['pending','anonymous']);
});
test('a completed session can authenticate without initiating scene entry itself',async()=>{
 const s=sessionSetup();s.resolve({user:{name:'existing'}});await settle();assert.deepEqual(s.auth,['pending','authenticated']);assert.equal(s.get('loading').dataset.sessionCheck,'complete');assert.equal(s.get('loading').dataset.entryRequested,undefined);
});
test('one primary action reveals credentials only after identity and preserves legacy password length',()=>{
 const nodes=new Map(),ctx={mode:'identify',user:null,$:id=>{if(!nodes.has(id))nodes.set(id,{setAttribute(){},value:'previous secret'});return nodes.get(id);}};
 vm.runInNewContext(source.slice(source.indexOf('function setMode('),source.indexOf('function openAccount(')),ctx);
 ctx.setMode('identify');assert.equal(ctx.$('socialSubmit').textContent,'继续');assert.equal(ctx.$('socialCredentialStep').hidden,true);assert.equal(ctx.$('socialPassword').disabled,true);assert.equal(ctx.$('socialPassword').value,'');
 ctx.setMode('login');assert.equal(ctx.$('socialSubmit').textContent,'继续');assert.equal(ctx.$('socialPassword').minLength,1);assert.equal(ctx.$('socialName').readOnly,true);
 ctx.setMode('register');assert.equal(ctx.$('socialSubmit').textContent,'创建并进入');assert.equal(ctx.$('socialPassword').minLength,8);assert.equal(ctx.$('socialPassword').autocomplete,'new-password');
 ctx.setMode('identify');assert.equal(ctx.$('socialName').readOnly,false);
});
