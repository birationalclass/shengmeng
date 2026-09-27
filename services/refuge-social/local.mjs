import http from 'node:http';
import {DatabaseSync} from 'node:sqlite';
import {createRequire} from 'node:module';
const require=createRequire(import.meta.url),{createHandler}=require('./service.cjs');
const db=new DatabaseSync(process.env.REFUGE_DB||':memory:');
db.exec('CREATE TABLE IF NOT EXISTS items(kind TEXT,id TEXT,value TEXT,PRIMARY KEY(kind,id))');
const store={
 async update(kind,id,value){await this.put(kind,id,{...await this.get(kind,id),...value});},
 async users(after){return db.prepare("SELECT value FROM items WHERE kind='users' AND id>? ORDER BY id LIMIT 51").all(after).map(r=>JSON.parse(r.value));},
 async get(kind,id){const row=db.prepare('SELECT value FROM items WHERE kind=? AND id=?').get(kind,id);return row?JSON.parse(row.value):null;},
 async put(kind,id,value){db.prepare('INSERT OR REPLACE INTO items VALUES(?,?,?)').run(kind,id,JSON.stringify(value));},
 async remove(kind,id){db.prepare('DELETE FROM items WHERE kind=? AND id=?').run(kind,id);},
 async create(kind,id,value){return db.prepare('INSERT OR IGNORE INTO items VALUES(?,?,?)').run(kind,id,JSON.stringify(value)).changes>0;},
 async rate(id,expiresAt){const old=await this.get('limits',id),count=(old?.count||0)+1;await this.put('limits',id,{count,expiresAt});return count;},
 async messages(){return db.prepare("SELECT value FROM items WHERE kind='messages'").all().map(r=>JSON.parse(r.value)).sort((a,b)=>b.createdAt-a.createdAt).slice(0,50);}
};
const handle=createHandler(store,{origins:['http://127.0.0.1:4203','http://localhost:4203'],secure:false});
http.createServer(async(req,res)=>{let raw='',size=0;for await(const chunk of req){size+=chunk.length;if(size>4096){res.writeHead(413);res.end();return;}raw+=chunk;}const r=await handle({httpMethod:req.method,path:new URL(req.url,'http://localhost').pathname,headers:req.headers,body:raw,trustedIp:req.socket.remoteAddress});res.writeHead(r.statusCode,r.headers);res.end(r.body);}).listen(8783,'127.0.0.1',()=>console.log('Refuge social development API on 8783'));
