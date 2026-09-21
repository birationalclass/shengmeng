import http from 'node:http';
import {isIP} from 'node:net';
import {DatabaseSync} from 'node:sqlite';
import {createHash,createHmac,randomBytes,timingSafeEqual} from 'node:crypto';
import {readFileSync,mkdirSync,chmodSync} from 'node:fs';
import {dirname,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createRequire} from 'node:module';
const require=createRequire(import.meta.url);
const model=require('../../courses/abstract-algebra/2026-fall/lesson-1/associativity-sudoku.js');
const hash=s=>createHash('sha256').update(String(s)).digest('hex');
const equal=(a,b)=>timingSafeEqual(Buffer.from(hash(a)),Buffer.from(hash(b)));
const fail=(status,message)=>Object.assign(new Error(message),{status});
export function verifiedBoards(boards){
 if(!boards||typeof boards!=='object'||Array.isArray(boards))return false;
 return Array.from({length:8},(_,i)=>i+2).every(n=>{const values=boards[n],clues=model.initial(n);return Array.isArray(values)&&values.length===n*n&&values.every((v,k)=>Number.isInteger(v)&&v>=1&&v<=n&&(!clues[k]||clues[k]===v))&&model.inspect(values).kind==='complete';});
}
export function createRecordsServer({dbPath,roster=[],secret,adminPassword,origins=['https://birationalclass.github.io'],trustedProxy=false,now=()=>Date.now()}={}){
 if(!secret||secret.length<32||!adminPassword||adminPassword.length<8)throw Error('Set a signing secret of at least 32 characters and an admin password of at least 8 characters.');
 if(dbPath!==':memory:'){mkdirSync(dirname(dbPath),{recursive:true,mode:0o700});}
 const db=new DatabaseSync(dbPath);if(dbPath!==':memory:')chmodSync(dbPath,0o600);
 db.exec(`PRAGMA journal_mode=WAL; PRAGMA foreign_keys=ON;
 CREATE TABLE IF NOT EXISTS students(id TEXT PRIMARY KEY,name TEXT NOT NULL,initials TEXT NOT NULL DEFAULT '');
 CREATE TABLE IF NOT EXISTS completions(student_id TEXT PRIMARY KEY REFERENCES students(id),first_at TEXT NOT NULL,updated_at TEXT NOT NULL,submission_id TEXT NOT NULL UNIQUE,boards TEXT NOT NULL);
 CREATE TABLE IF NOT EXISTS requests(id TEXT PRIMARY KEY,student_id TEXT NOT NULL,created_at TEXT NOT NULL);
 `);
 if(!db.prepare('PRAGMA table_info(students)').all().some(c=>c.name==='initials'))db.exec("ALTER TABLE students ADD COLUMN initials TEXT NOT NULL DEFAULT ''");
 const upsert=db.prepare('INSERT INTO students(id,name,initials) VALUES (?,?,?) ON CONFLICT(id) DO UPDATE SET name=excluded.name,initials=excluded.initials');
 db.exec('BEGIN');try{for(const r of roster){if(!/^\d{11}$/.test(r.id)||typeof r.name!=='string'||!r.name.trim()||r.name.length>80||typeof r.initials!=='string'||! /^[A-Z]{1,80}$/.test(r.initials))throw Error('Invalid roster');upsert.run(r.id,r.name.trim(),r.initials);}db.exec('COMMIT');}catch(e){db.exec('ROLLBACK');db.close();throw e;}
 const limits=new Map();
 function rate(ip,scope,max){const key=hash(ip)+'/'+scope,minute=Math.floor(now()/60000),old=limits.get(key),r=old?.minute===minute?old:{minute,count:0};r.count++;limits.set(key,r);if(limits.size>10000)for(const [k,v]of limits)if(v.minute<minute-1)limits.delete(k);if(r.count>max)throw fail(429,'操作过于频繁，请一分钟后再试。');}
 function sign(value){const body=Buffer.from(JSON.stringify(value)).toString('base64url');return body+'.'+createHmac('sha256',secret).update(body).digest('base64url');}
 function unpack(token,kind){try{const [body,sig]=String(token).split('.');if(!equal(sig,createHmac('sha256',secret).update(body).digest('base64url')))return null;const v=JSON.parse(Buffer.from(body,'base64url'));return v.kind===kind&&v.exp>now()?v:null;}catch{return null;}}
 function student(id){if(typeof id!=='string'||!/^\d{11}$/.test(id))throw fail(400,'请输入完整的 11 位学号。');const row=db.prepare('SELECT id,name FROM students WHERE id=?').get(id);if(!row)throw fail(404,'点名册中没有这个学号，请核对后重试。');return row;}
 const result=(id,full=false)=>{const r=db.prepare('SELECT s.id,s.name,s.initials,c.first_at,c.updated_at FROM completions c JOIN students s ON s.id=c.student_id WHERE s.id=?').get(id);return r?{studentId:full?r.id:r.id.slice(0,3)+'****'+r.id.slice(-4),name:full?r.name:(r.initials||'—'),firstCompletedAt:r.first_at,updatedAt:r.updated_at,completedLevels:8}:null;};
 async function body(req){if(!/^application\/json\b/i.test(req.headers['content-type']||''))throw fail(415,'请使用 JSON 请求。');let size=0,parts=[];for await(const part of req){size+=part.length;if(size>16384)throw fail(413,'提交内容过大。');parts.push(part);}try{const value=JSON.parse(Buffer.concat(parts).toString());if(!value||typeof value!=='object'||Array.isArray(value))throw Error('object required');return value;}catch{throw fail(400,'请求格式不正确。');}}
 const server=http.createServer(async(req,res)=>{
  res.setHeader('Content-Type','application/json; charset=utf-8');res.setHeader('Cache-Control','no-store');res.setHeader('X-Content-Type-Options','nosniff');res.setHeader('Vary','Origin');
  const origin=req.headers.origin,peer=req.socket.remoteAddress||'unknown',forwarded=req.headers['x-real-ip'];
  const ip=trustedProxy&&['127.0.0.1','::1','::ffff:127.0.0.1'].includes(peer)&&typeof forwarded==='string'&&isIP(forwarded)?forwarded:peer;
  const send=(status,value)=>{res.writeHead(status);res.end(JSON.stringify(value));};
  try{
   if(origin&&!origins.includes(origin))throw fail(403,'此来源不允许访问。');
   if(origin)res.setHeader('Access-Control-Allow-Origin',origin);
   if(req.method==='OPTIONS'){res.setHeader('Access-Control-Allow-Methods','GET,POST,OPTIONS');res.setHeader('Access-Control-Allow-Headers','Content-Type,Authorization');return send(204,undefined);}
   const path=new URL(req.url,'http://localhost').pathname,token=(req.headers.authorization||'').replace(/^Bearer /,'');
   if(req.method==='GET'&&path==='/api/health')return send(200,{ready:true,idLength:11});
   if(req.method==='POST'&&path==='/api/lookup'){
    rate(ip,'lookup',20);const input=await body(req),s=student(input.studentId);
    return send(200,{name:s.name,lookupToken:sign({kind:'lookup',id:s.id,exp:now()+5*60000})});
   }
   if(req.method==='POST'&&path==='/api/completions'){
    rate(ip,'submit',12);const input=await body(req),s=student(input.studentId),lookup=unpack(input.lookupToken,'lookup');
    if(!lookup||lookup.id!==s.id)throw fail(401,'姓名查询已过期，请重新输入学号。');
    if(input.name!==s.name)throw fail(400,'姓名与点名册不一致，请重新核对。');
    if(!/^[a-f0-9-]{36}$/i.test(input.submissionId||''))throw fail(400,'缺少提交编号。');
    if(!verifiedBoards(input.boards))throw fail(400,'请先完成 2×2 至 9×9 全部关卡。');
    const previous=db.prepare('SELECT student_id FROM requests WHERE id=?').get(input.submissionId);if(previous&&previous.student_id!==s.id)throw fail(409,'提交编号已使用。');
    const timestamp=new Date(now()).toISOString();
    db.exec('BEGIN IMMEDIATE');try{
     if(!previous){db.prepare('INSERT INTO completions(student_id,first_at,updated_at,submission_id,boards) VALUES (?,?,?,?,?) ON CONFLICT(student_id) DO UPDATE SET updated_at=excluded.updated_at,submission_id=excluded.submission_id,boards=excluded.boards').run(s.id,timestamp,timestamp,input.submissionId,JSON.stringify(input.boards));db.prepare('INSERT INTO requests(id,student_id,created_at) VALUES (?,?,?)').run(input.submissionId,s.id,timestamp);}
     db.exec('COMMIT');
    }catch(e){db.exec('ROLLBACK');throw e;}
    return send(200,{saved:true,record:result(s.id)});
   }
   if(req.method==='GET'&&path==='/api/records'){
    rate(ip,'records',45);const ids=db.prepare('SELECT student_id FROM completions ORDER BY first_at ASC').all();return send(200,{records:ids.map(r=>result(r.student_id)),total:ids.length});
   }
   if(req.method==='POST'&&path==='/api/admin/session'){
    rate(ip,'admin',5);const input=await body(req);if(!equal(input.password||'',adminPassword))throw fail(401,'教师口令不正确。');return send(200,{token:sign({kind:'admin',exp:now()+30*60000})});
   }
   if(req.method==='GET'&&path==='/api/admin/records'){
    if(!unpack(token,'admin'))throw fail(401,'请先进行教师登录。');const rows=db.prepare('SELECT student_id FROM completions ORDER BY updated_at DESC').all();return send(200,{records:rows.map(r=>result(r.student_id,true)),total:rows.length});
   }
   throw fail(404,'未找到此接口。');
  }catch(e){send(e.status||500,{error:e.status?e.message:'暂时无法保存，请稍后重试。'});}
 });
 server.requestTimeout=15000;server.headersTimeout=10000;
 return {server,db,close:()=>new Promise(resolve=>server.close(()=>{db.close();resolve();}))};
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){
 const roster=process.env.RECORDS_ROSTER?JSON.parse(readFileSync(process.env.RECORDS_ROSTER,'utf8')):[];
 const {server}=createRecordsServer({dbPath:process.env.RECORDS_DB,roster,secret:process.env.RECORDS_SECRET,adminPassword:process.env.RECORDS_ADMIN_PASSWORD,origins:(process.env.RECORDS_ORIGINS||'https://birationalclass.github.io').split(','),trustedProxy:process.env.RECORDS_TRUST_PROXY==='1'});
 server.listen(Number(process.env.PORT||8782),process.env.HOST||'127.0.0.1',()=>console.log('Group Sudoku records API ready'));
}
