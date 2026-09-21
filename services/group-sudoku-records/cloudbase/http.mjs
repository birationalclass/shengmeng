import {handle} from './service.mjs';
export async function handleHttp(event,env,now=Date.now()){
 const requestHeaders=Object.fromEntries(Object.entries(event.headers||{}).map(([key,value])=>[key.toLowerCase(),value]));
 const origin=requestHeaders.origin,allowed=(env.origins||'https://birationalclass.github.io').split(',');
 const headers={'Content-Type':'application/json; charset=utf-8','Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Vary':'Origin'};
 const send=(status,data)=>({statusCode:status,headers,body:status===204?'':JSON.stringify(data),isBase64Encoded:false});
 if(origin&&!allowed.includes(origin))return send(403,{error:'此来源不允许访问。'});
 if(origin)headers['Access-Control-Allow-Origin']=origin;
 if(event.httpMethod==='OPTIONS'){
  headers['Access-Control-Allow-Methods']='GET,POST,OPTIONS';headers['Access-Control-Allow-Headers']='Content-Type,Authorization';return send(204);
 }
 let body;
 if(event.httpMethod==='POST'){
  if(!/^application\/json\b/i.test(requestHeaders['content-type']||''))return send(415,{error:'请使用 JSON 请求。'});
  if(typeof event.body!=='string'||event.body.length>24000)return send(413,{error:'提交内容过大。'});
  try{const text=event.isBase64Encoded?Buffer.from(event.body,'base64').toString('utf8'):event.body;if(Buffer.byteLength(text)>16384)return send(413,{error:'提交内容过大。'});body=JSON.parse(text);}catch{return send(400,{error:'请求格式不正确。'});}
 }
 const path=(event.path||'').replace(/^\/records(?:-test)?(?=\/|$)/,'');
 const result=await handle({path,method:event.httpMethod,body,token:(requestHeaders.authorization||'').replace(/^Bearer /,'')},env,now);
 return send(result.status,result.data);
}
