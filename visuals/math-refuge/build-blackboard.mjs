import {createRequire} from 'node:module';
import {readFileSync,writeFileSync} from 'node:fs';
import {dirname,resolve,relative} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
const root=dirname(fileURLToPath(import.meta.url)),require=createRequire(import.meta.url),esbuild=require(process.argv[2]||'esbuild');
const result=await esbuild.build({absWorkingDir:root,entryPoints:{'blackboard-bundle':'blackboard-app.js'},bundle:true,splitting:true,format:'esm',target:'es2022',outdir:root,chunkNames:'blackboard-chunk-[hash]',minify:true,metafile:true,plugins:[{name:'local-shared-board',setup(build){
 build.onResolve({filter:/.*/},a=>{if(a.kind==='entry-point')return{path:resolve(root,a.path)};if(a.path==='three'||/three\.module\.js(?:\?|$)/.test(a.path))return{path:resolve(root,'../3d/vendor/three.module.js')};const s=a.path.replace(/\?.*$/,'');if(s.startsWith('three/addons/'))return{path:resolve(root,'vendor',s.slice(13))};if(s.startsWith('.'))return{path:resolve(a.resolveDir,s)};});
 build.onLoad({filter:/\.js$/},a=>{let contents=readFileSync(a.path,'utf8'),rel=relative(root,a.path);if(rel.startsWith('../')&&contents.includes('import.meta.url'))contents=contents.replaceAll('import.meta.url',`new URL(${JSON.stringify(rel)},import.meta.url).href`);return{contents,loader:'js',resolveDir:dirname(a.path)};});
}}]});
const outputs=Object.entries(result.metafile.outputs).map(([path,v])=>({path,bytes:v.bytes,inputs:Object.keys(v.inputs),imports:v.imports}));
writeFileSync(resolve(root,'blackboard-bundles.json'),JSON.stringify({outputs},null,2)+'\n');
const hash=n=>createHash('sha256').update(readFileSync(resolve(root,n))).digest('hex').slice(0,12),html=resolve(root,'../blackboard/index.html');
writeFileSync(html,readFileSync(html,'utf8').replace(/blackboard-bundle\.js(?:\?v=[a-f0-9]+)?/g,'blackboard-bundle.js?v='+hash('blackboard-bundle.js')).replace(/blackboard\.css(?:\?v=[a-f0-9]+)?/g,'blackboard.css?v='+hash('blackboard.css')));
console.log(JSON.stringify({outputs:outputs.length,bytes:outputs.reduce((n,v)=>n+v.bytes,0)}));
