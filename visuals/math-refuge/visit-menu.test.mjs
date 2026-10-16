import test from 'node:test';
import assert from 'node:assert/strict';
import {bindVisitMenu} from './visit-menu.js';
class Element extends EventTarget{constructor(){super();this.dataset={};this.hidden=false;this.attrs={};}setAttribute(k,v){this.attrs[k]=v;}contains(v){return v===this;}focus(){this.focused=true;}}
test('visitor menu stays open for three seconds after leaving, return cancels collapse',()=>{
 const dock=new Element(),button=new Element(),panel=new Element();let now=0,id=0;const timers=new Map();
 bindVisitMenu(dock,button,panel,{setTimer:fn=>{timers.set(++id,{fn,at:now+3000});return id;},clearTimer:id=>timers.delete(id)});
 const advance=ms=>{now+=ms;for(const [id,t]of timers)if(t.at<=now){timers.delete(id);t.fn();}};
 assert.equal(panel.hidden,true);button.dispatchEvent(new Event('click'));assert.equal(panel.hidden,false);
 dock.dispatchEvent(new Event('pointerleave'));advance(2999);assert.equal(panel.hidden,false);
 dock.dispatchEvent(new Event('pointerenter'));advance(2);assert.equal(panel.hidden,false);
 dock.dispatchEvent(new Event('pointerleave'));advance(3000);assert.equal(panel.hidden,true);assert.equal(button.attrs['aria-expanded'],'false');
});
test('escape closes menu and returns keyboard focus to trigger',()=>{
 const dock=new Element(),button=new Element(),panel=new Element();bindVisitMenu(dock,button,panel);button.dispatchEvent(new Event('click'));
 const e=new Event('keydown');e.key='Escape';dock.dispatchEvent(e);assert.equal(panel.hidden,true);assert(button.focused);
});
