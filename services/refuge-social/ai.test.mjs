import {test} from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
const {createAI}=createRequire(import.meta.url)('./ai.cjs');
test('encrypted credentials remain server-only and provider adapters carry vision input',async()=>{
 const map=new Map(),calls=[],store={get:async(k,id)=>map.get(id),put:async(k,id,v)=>map.set(id,v)};
 const ai=createAI(store,{secret:'test-secret-'.repeat(4),fetcher:async(url,opt)=>{calls.push({url,...opt});return {ok:true,json:async()=>url.includes('dashscope')?{choices:[{message:{content:'Qwen answer'}}]}:{id:'resp_test',status:'completed',output:[{content:[{type:'output_text',text:'OpenAI answer'}]}]}};}});
 const key='test-api-key-never-public-12345';
 await assert.rejects(ai.start({provider:'openai'}),/配置/);
 for(const provider of ['openai','qwen']){await ai.save({provider,key,model:'test-model'});const r=await ai.start({provider,image:'data:image/jpeg;base64,test',question:'question'});assert.equal(r.status,'completed');}
 assert.ok(!JSON.stringify([...map.values()]).includes(key));assert.ok(!JSON.stringify(await ai.list()).includes(key));
 assert.equal(calls[0].headers.Authorization,'Bearer '+key);assert.equal(JSON.parse(calls[0].body).input[0].content[1].type,'input_image');
 assert.equal(JSON.parse(calls[1].body).messages[1].content[1].type,'image_url');
});
