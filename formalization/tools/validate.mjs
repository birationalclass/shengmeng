// Run from any directory: node formalization/tools/validate.mjs
import {readFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';
import {resolve,dirname} from 'node:path';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
import {nodes} from '../negativity/graph-data.js';
const base=resolve(dirname(fileURLToPath(import.meta.url)),'../negativity');
const snapshot=JSON.parse(readFileSync(resolve(base,'snapshot.json'),'utf8'));
const ids=new Set(nodes.map(n=>n.id));assert.equal(ids.size,nodes.length);
const visiting=new Set(),done=new Set();
function visit(id){assert(ids.has(id),'Unknown dependency: '+id);assert(!visiting.has(id),'Dependency cycle: '+id);if(done.has(id))return;visiting.add(id);nodes.find(n=>n.id===id).deps.forEach(visit);visiting.delete(id);done.add(id)}
nodes.forEach(n=>{visit(n.id);if(['done','conditional'].includes(n.status))assert(snapshot.declarations[n.decl],'Missing source declaration');else assert(!n.decl,'Unproved node claims source')});
for(const f of snapshot.files){const data=readFileSync(resolve(base,'source',f.path));assert.equal(createHash('sha256').update(data).digest('hex'),f.sha256,'Stale source snapshot: '+f.path)}
for(const d of Object.values(snapshot.declarations)){const lines=readFileSync(resolve(base,'source',d.path),'utf8').replace(/^\uFEFF/,'').split(/\r?\n/);assert.equal(lines.slice(d.line-1,d.line-1+d.code.split('\n').length).join('\n').trim(),d.code,'Stale declaration excerpt')}
console.log('Verified DAG, source hashes, declaration excerpts and status/source mapping.');
