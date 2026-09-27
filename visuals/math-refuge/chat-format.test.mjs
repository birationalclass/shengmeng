import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import vm from 'node:vm';
const source=readFileSync(new URL('./chat-format.js',import.meta.url),'utf8').replace('export function','function');
test('untrusted HTML stays text; math receives safe KaTeX options',()=>{
 const node=tag=>({tag,children:[],append(...c){this.children.push(...c);},replaceChildren(){this.children=[];}}),calls=[];
 const ctx={document:{createElement:node,createTextNode:text=>({text})},window:{katex:{render:(text,target,options)=>calls.push({text,options})}}};
 vm.runInNewContext(source,ctx);const container=node('div');ctx.renderChatText(container,'<img src=x onerror=alert(1)> **bold** $x^2$ \\[a+b\\]');
 assert.match(container.children[0].text,/<img/);assert.equal(container.children.filter(n=>n.tag==='img').length,0);assert.equal(calls.length,2);assert.equal(calls[0].options.trust,false);assert.equal(calls[1].options.displayMode,true);
});
