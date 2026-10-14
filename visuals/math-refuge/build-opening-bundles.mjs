// Run: node build-opening-bundles.mjs <path to installed esbuild package>
// All chunks remain beside the sources, preserving relative assets/import.meta.url.
import {createRequire} from 'node:module';
import {readFileSync,writeFileSync,existsSync} from 'node:fs';
import {dirname,resolve,relative,sep} from 'node:path';
import {fileURLToPath} from 'node:url';
const require=createRequire(import.meta.url),esbuild=require(process.argv[2]||'esbuild');
const root=dirname(fileURLToPath(import.meta.url));
const oldManifest=existsSync(resolve(root,'opening-bundles.json'))?JSON.parse(readFileSync(resolve(root,'opening-bundles.json'),'utf8')):{};
const plugin={name:'refuge-local-modules',setup(build){
 build.onResolve({filter:/.*/},args=>{
  if(args.kind==='entry-point')return {path:resolve(root,args.path)};
  if(args.path==='three'||/three\.module\.js(?:\?|$)/.test(args.path))return {path:resolve(root,'../3d/vendor/three.module.js')};
  const spec=args.path.replace(/\?.*$/,'');
  if(spec.startsWith('three/addons/'))return {path:resolve(root,'vendor',spec.slice(13))};
  if(spec.startsWith('.'))return {path:resolve(args.resolveDir,spec)};
 });
 build.onLoad({filter:/\.js$/},async args=>{
  let contents=readFileSync(args.path,'utf8');
  const rel=relative(root,args.path).split(sep).join('/');
  if(rel.startsWith('../')&&contents.includes('import.meta.url'))contents=contents.replaceAll('import.meta.url',`new URL(${JSON.stringify(rel)},import.meta.url).href`);
  return {contents,loader:'js',resolveDir:dirname(args.path)};
 });
}};
const result=await esbuild.build({absWorkingDir:root,entryPoints:{'refuge-app':'app.js','refuge-social':'social.js','refuge-meter':'loading-transfer.js'},bundle:true,splitting:true,format:'esm',target:'es2022',outdir:root,entryNames:'[name]',chunkNames:'refuge-chunk-[hash]',minify:true,metafile:true,legalComments:'eof',plugins:[plugin]});
const outputs=Object.entries(result.metafile.outputs).map(([path,o])=>({path,bytes:o.bytes,imports:o.imports,inputs:Object.keys(o.inputs)}));
let html=readFileSync(resolve(root,'index.html'),'utf8');
const styles=[...html.matchAll(/<link\b[^>]*rel="stylesheet"[^>]*href="([^"?]+)(?:\?[^\"]*)?"[^>]*>/g)];
const styleSources=styles.length>1?styles.map(m=>m[1]):oldManifest.styleSources||['style.css','coastal-layout.css','chalk-reader.css','board-console.css','control-dock.css','atmosphere.css','panel-shell.css','residence.css','performance-monitor.css','arrival.css','screen-webview.css','graphics-settings.css','social.css'];
writeFileSync(resolve(root,'refuge-style.css'),styleSources.map(name=>readFileSync(resolve(root,name),'utf8')).join('\n'));
writeFileSync(resolve(root,'opening-bundles.json'),JSON.stringify({outputs,styleSources},null,2)+'\n');
let first=true;html=html.replace(/<link\b[^>]*rel="stylesheet"[^>]*href="([^"?]+)(?:\?[^\"]*)?"[^>]*>/g,()=>first?(first=false,'<link rel="stylesheet" href="refuge-style.css?v=opening-fast-1">'):'');
html=html.replace(/(?<!refuge-)app\.js\?v=[\w-]+/g,'refuge-app.js?v=opening-fast-1').replace(/src="social\.js\?v=[\w-]+"/,'src="refuge-social.js?v=opening-fast-1"').replace(/src="loading-transfer\.js\?v=[\w-]+"/,'src="refuge-meter.js?v=opening-fast-1"');
const staticFiles=new Set();
function critical(path){if(staticFiles.has(path))return;staticFiles.add(path);const output=result.metafile.outputs[path];for(const item of output?.imports||[])if(item.kind==='import-statement'&&!item.external)critical(item.path);}
critical('refuge-app.js');critical('refuge-social.js');critical('refuge-meter.js');
html=html.replace(/\n?\s*<link\b[^>]*data-refuge-bundle[^>]*>/g,'');
html=html.replace('</head>',[...staticFiles].filter(p=>p.startsWith('refuge-chunk-')).map(p=>`  <link rel="modulepreload" data-refuge-bundle href="${p}">`).join('\n')+'\n</head>');
writeFileSync(resolve(root,'index.html'),html);
console.log(JSON.stringify({outputs:outputs.length,bytes:outputs.reduce((a,b)=>a+b.bytes,0)}));
