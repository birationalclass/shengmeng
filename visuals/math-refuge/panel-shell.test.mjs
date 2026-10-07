import test from 'node:test';import assert from 'node:assert/strict';import {bindPanelDismissals} from './panel-shell.js';
const node=()=>({hidden:false,contains:t=>t?.inside===true});
function click(doc,path,button=0){const e=new Event('click');Object.defineProperty(e,'composedPath',{value:()=>path});Object.defineProperty(e,'button',{value:button});doc.dispatchEvent(e);}
test('outside click closes panels while internal controls and their opener remain usable',()=>{
 const doc=new EventTarget(),panel=node(),trigger={contains:()=>false};let closed=0;const dispose=bindPanelDismissals(doc,[{panel,triggers:[trigger],close:()=>closed++}]);
 click(doc,[panel]);click(doc,[trigger]);click(doc,[],2);assert.equal(closed,0);click(doc,[]);assert.equal(closed,1);panel.hidden=true;click(doc,[]);assert.equal(closed,1);dispose();panel.hidden=false;click(doc,[]);assert.equal(closed,1);
});
test('clicking a different panel dismisses only the previous panel',()=>{
 const doc=new EventTarget(),a=node(),b=node(),closed=[];bindPanelDismissals(doc,[{panel:a,close:()=>closed.push('a')},{panel:b,close:()=>closed.push('b')}]);click(doc,[b]);assert.deepEqual(closed,['a']);
});
