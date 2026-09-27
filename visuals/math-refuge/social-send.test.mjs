import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';
import {randomUUID} from 'node:crypto';
const source=readFileSync(new URL('./social.js',import.meta.url),'utf8');
const code=source.slice(source.indexOf('function sendOptimistic('),source.indexOf("\nwindow.addEventListener('keydown'"));
function setup(){
 const node=()=>({children:[],append(...nodes){for(const n of nodes){n.parent=this;this.children.push(n);}},remove(){this.parent.children.splice(this.parent.children.indexOf(this),1);},setAttribute(k,v){this[k]=v;},focus(){}});
 const elements={socialMessages:node(),socialInput:{...node(),value:''},socialComposer:node()},calls=[],confirmed=[];
 const ctx={renderChatText:(node,text)=>node.textContent=text,document:{createElement:node},$:id=>elements[id],crypto:{randomUUID},generation:1,user:{name:'test'},activity(){},fadeMessage(){},message:e=>e.message,addMessages:items=>confirmed.push(...items),request:(path,payload)=>new Promise((resolve,reject)=>calls.push({path,payload,resolve,reject}))};
 vm.runInNewContext(code,ctx);return {elements,calls,confirmed,send(text){elements.socialInput.value=text;elements.socialComposer.onsubmit({preventDefault(){}});}};
}
const settle=()=>new Promise(resolve=>setImmediate(resolve));
test('messages appear immediately; consecutive sends do not block; server timestamp replaces provisional time',async()=>{
 const s=setup();s.send('first');assert.equal(s.elements.socialInput.value,'');assert.equal(s.elements.socialMessages.children.length,1);assert.equal(s.elements.socialMessages.children[0].children[3].className,'social-sending');
 s.send('second');assert.equal(s.calls.length,2);assert.equal(s.elements.socialMessages.children.length,2);
 s.calls[0].resolve({message:{id:'server-first',createdAt:1234567890000,text:'first'}});await settle();assert.equal(s.confirmed[0].createdAt,1234567890000);assert.equal(s.elements.socialMessages.children.length,1);
});
test('failure retains the message and retries the same idempotency key',async()=>{
 const s=setup();s.send('retry me');s.calls[0].reject(new Error('offline'));await settle();const button=s.elements.socialMessages.children[0].children[3];assert.equal(button.className,'social-send-retry');assert.equal(button.disabled,false);button.onclick();assert.equal(s.calls[0].payload.id,s.calls[1].payload.id);assert.equal(s.elements.socialMessages.children.length,1);
});
