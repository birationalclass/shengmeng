import test from 'node:test';import assert from 'node:assert/strict';import vm from 'node:vm';import {readFileSync} from 'node:fs';
const source=readFileSync(new URL('./blackboard-app.js',import.meta.url),'utf8'),method=source.split('\n').find(s=>s.startsWith('async function selectReport('));
for(const autoplay of [true,false])test('selection forwards autoplay='+autoplay+' to the existing transport without toggling during loading',async()=>{
 const calls=[],lecture={report:{kind:'classroom',narration:{defaultPlaybackRate:1}},async setReport(id,options){calls.push(['select',id,options.autoplay]);},async setLanguage(v){calls.push(['language',v]);},setVoiceRate(v){calls.push(['rate',v]);},toggleVoice(){assert.fail('a loading toggle cancels automatic playback');}};
 const context={lecture,selecting:false,lastPageKey:'',webview:{close(){}},updateUI(){},focus(){},$:()=>({textContent:''})};vm.createContext(context);vm.runInContext(method+';this.run=selectReport;',context);assert.equal(await context.run('sylow-theorems',{autoplay}),true);assert.deepEqual(calls[0],['select','sylow-theorems',autoplay]);assert.equal(context.selecting,false);
});
test('Visual directory retains every previous project and adds a searchable board entry with correct counts',()=>{
 const html=readFileSync(new URL('../index.html',import.meta.url),'utf8');assert.equal((html.match(/<article class="project" /g)||[]).length,16);assert(html.includes('href="./blackboard/"'));assert(html.includes('交互与工具<span>5</span>'));assert(html.includes('16 个项目'));
});
