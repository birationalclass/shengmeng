import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';
const source=readFileSync(new URL('./social.js',import.meta.url),'utf8');
test('one primary action reveals credentials only after identity and preserves legacy password length',()=>{
 const nodes=new Map(),ctx={mode:'identify',user:null,$:id=>{if(!nodes.has(id))nodes.set(id,{setAttribute(){},value:'previous secret'});return nodes.get(id);}};
 vm.runInNewContext(source.slice(source.indexOf('function setMode('),source.indexOf('function openAccount(')),ctx);
 ctx.setMode('identify');assert.equal(ctx.$('socialSubmit').textContent,'继续');assert.equal(ctx.$('socialCredentialStep').hidden,true);assert.equal(ctx.$('socialPassword').disabled,true);assert.equal(ctx.$('socialPassword').value,'');
 ctx.setMode('login');assert.equal(ctx.$('socialSubmit').textContent,'继续');assert.equal(ctx.$('socialPassword').minLength,1);assert.equal(ctx.$('socialName').readOnly,true);
 ctx.setMode('register');assert.equal(ctx.$('socialSubmit').textContent,'创建并进入');assert.equal(ctx.$('socialPassword').minLength,8);assert.equal(ctx.$('socialPassword').autocomplete,'new-password');
 ctx.setMode('identify');assert.equal(ctx.$('socialName').readOnly,false);
});
