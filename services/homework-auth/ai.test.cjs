const test=require('node:test'),assert=require('node:assert/strict');
const {createAI}=require('./ai.cjs');
const stream=events=>new Response(events.map(e=>'data: '+JSON.stringify(e)+'\r\n\r\n').join(''));
test('background creation uses vision, strict schema and medium reasoning',async()=>{
 let body;const ai=createAI({apiKey:'fixture',fetcher:async(url,options)=>{assert.equal(url,'https://api.openai.com/v1/responses');body=JSON.parse(options.body);return stream([{type:'response.created',sequence_number:0,response:{id:'resp_fixture'}}]);}});
 assert.deepEqual(await ai.start({phase:'recognize',pages:[{data:'/9j/2Q=='}],requestId:'fixture'}),{id:'resp_fixture',cursor:0});
 assert.equal(body.background,true);assert.equal(body.reasoning.effort,'medium');assert.equal(body.text.format.strict,true);assert.equal(body.input[0].content[1].type,'input_image');
});
test('completed response restores final output and actual usage without another stream',async()=>{
 let calls=0;const usage={input_tokens:10,output_tokens:20};const ai=createAI({apiKey:'fixture',fetcher:async()=>{calls++;return Response.json({status:'completed',output:[{content:[{type:'output_text',text:'{}'}]}],usage});}});
 const result=await ai.poll('resp_fixture',4);assert.equal(calls,1);assert.equal(result.text,'{}');assert.deepEqual(result.usage,usage);
});
test('in-progress response resumes after prior sequence and returns deltas',async()=>{
 let calls=0;const ai=createAI({apiKey:'fixture',fetcher:async url=>{if(!calls++)return Response.json({status:'in_progress'});assert.match(url,/starting_after=3$/);return stream([{type:'response.output_text.delta',sequence_number:4,delta:'part'}]);}});
 assert.deepEqual(await ai.poll('resp_fixture',3),{status:'in_progress',delta:'part',cursor:4});
});
test('provider errors never expose upstream body or credentials',async()=>{
 const ai=createAI({apiKey:'fixture',fetcher:async()=>new Response('private provider detail',{status:401})});
 await assert.rejects(ai.poll('resp_fixture'),e=>e.status===503&&!e.message.includes('private'));
});
