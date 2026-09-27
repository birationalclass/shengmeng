const {createHash,randomBytes,createCipheriv,createDecipheriv}=require('node:crypto');
const encryptionKey=secret=>createHash('sha256').update('homework-ai-settings:'+secret).digest();
function encrypt(value,secret){const iv=randomBytes(12),cipher=createCipheriv('aes-256-gcm',encryptionKey(secret),iv);const data=Buffer.concat([cipher.update(value,'utf8'),cipher.final()]);return {iv:iv.toString('hex'),tag:cipher.getAuthTag().toString('hex'),data:data.toString('base64')};}
function decrypt(value,secret){const decipher=createDecipheriv('aes-256-gcm',encryptionKey(secret),Buffer.from(value.iv,'hex'));decipher.setAuthTag(Buffer.from(value.tag,'hex'));return Buffer.concat([decipher.update(Buffer.from(value.data,'base64')),decipher.final()]).toString('utf8');}
async function loadKey(store,secret){const saved=await store.get('settings','openai');return saved?.encrypted?decrypt(saved.encrypted,secret):process.env.OPENAI_API_KEY||'';}
async function saveKey(store,secret,key){
 if(typeof key!=='string'||key.length<20||key.length>500||!key.startsWith('sk-')||/\s/.test(key))throw Object.assign(Error('请输入有效的 OpenAI API key。'),{status:400});
 let response;try{response=await fetch('https://api.openai.com/v1/models/gpt-6-sol',{headers:{Authorization:'Bearer '+key},signal:AbortSignal.timeout(12000)});}catch{throw Object.assign(Error('服务器暂时无法连接 OpenAI，密钥尚未保存。'),{status:503});}
 if(!response.ok)throw Object.assign(Error('密钥验证失败，或该账号尚不能访问 gpt-6-sol。'),{status:400});
 await store.put('settings','openai',{encrypted:encrypt(key,secret),updatedAt:Date.now()});
}
module.exports={loadKey,saveKey,encrypt,decrypt};
