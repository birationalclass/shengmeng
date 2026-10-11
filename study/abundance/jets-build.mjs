import {readFile,writeFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
const root=new URL('./',import.meta.url);
const d=JSON.parse(await readFile(new URL('jets-content.json',root),'utf8'));
const source=await readFile(new URL(d.source,root));
if(createHash('sha256').update(source).digest('hex')!==d.sourceSha256)throw Error('Jets source changed; extract current manuscript before building');
const escape=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const refs=new Map(),bib=new Map(),equations=new Map();let equation=0,currentHeading=null;
function index(blocks){
 for(const b of blocks){
  b.id=b.type==='setup'?'setup-framework':b.type==='thebibliography'?'references':b.number?`${b.type}-${b.number}`:b.type==='section'?'sources':null;
  if(b.type==='section'||b.type==='subsection')currentHeading=b;
  if(b.type==='thebibliography'){
   b.items=[...b.content.matchAll(/\\bibitem\{([^{}]+)\}([\s\S]*?)(?=\\bibitem\{|$)/g)].map((m,i)=>({key:m[1],number:i+1,content:m[2].trim()}));
   b.items.forEach(item=>bib.set(item.key,item));
  }
  // Introduction and completion occur in this order in the TeX proof.
  if(b.introduction)index(b.introduction);
  for(const m of (b.content||'').matchAll(/\\begin\{equation\}([\s\S]*?)\\end\{equation\}/g)){
   if(equations.has(m[0]))throw Error('Duplicate equation source');
   const num=++equation;equations.set(m[0],{number:num,id:`equation-${num}`});
   for(const label of m[1].matchAll(/\\label\{([^{}]+)\}/g))refs.set(label[1],{number:String(num),target:`equation-${num}`});
  }
  for(const label of (b.content||'').replace(/\\begin\{equation\}[\s\S]*?\\end\{equation\}/g,'').matchAll(/\\label\{([^{}]+)\}/g)){
   const target=b.id||currentHeading?.id;
   if(!target)throw Error(`Label without target: ${label[1]}`);
   if(refs.has(label[1]))throw Error('Duplicate label: '+label[1]);
   refs.set(label[1],{target,number:b.number||currentHeading?.number||''});
  }
 }
}
index(d.blocks);
if(equation!==d.structure.equations||refs.size!==d.structure.labels||bib.size!==d.structure.bibliography)throw Error('Source counts do not match rendered references');
const ref=(key)=>{const r=refs.get(key);if(!r)throw Error(`Unknown reference: ${key}`);return r};
function math(tex,display){
 tex=tex.replace(/\\label\{[^{}]+\}/g,'').replace(/\\(begin|end)\{split\}/g,'\\$1{aligned}');
 tex=tex.replace(/\\(eqref|ref)\{([^{}]+)\}/g,(_,kind,key)=>{const r=ref(key);return `\\href{#${r.target}}{${kind==='eqref'?'('+r.number+')':r.number}}`});
 return `<span class="math-source" data-display="${display}" data-math="${escape(tex.trim())}"></span>`;
}
function argument(s,start){
 if(s[start]!=='{')throw Error('Expected balanced prose argument: '+s.slice(start,start+60));
 let depth=1,i=start+1;for(;i<s.length;i++){if(s[i]==='{'&&s[i-1]!=='\\')depth++;if(s[i]==='}'&&s[i-1]!=='\\'&&!--depth)return {value:s.slice(start+1,i),end:i+1};}
 throw Error('Unclosed prose argument');
}
function prose(s){
 s=s.replace(/\\'\{?([a-zA-Z])\}?/g,(_,c)=>({e:'é',E:'É',c:'ć',a:'á',o:'ó'}[c]||c))
    .replace(/\\"\{?([a-zA-Z])\}?/g,(_,c)=>({a:'ä',o:'ö',u:'ü'}[c]||c))
    .replace(/\\u\{([a-zA-Z])\}/g,(_,c)=>({c:'č'}[c]||c));
 let result='',i=0;
 while(i<s.length){
  if(s[i]!=='\\'){let end=s.indexOf('\\',i);if(end<0)end=s.length;result+=escape(s.slice(i,end).replace(/~/g,' ').replace(/\s+/g,' ').replace(/``/g,'“').replace(/''/g,'”').replace(/--/g,'–'));i=end;continue;}
  const command=/^\\([a-zA-Z]+)/.exec(s.slice(i));if(!command)throw Error('Unsupported prose escape: '+s.slice(i,i+70));
  const name=command[1];i+=command[0].length;
  if(['smallskip','noindent','leavevmode','qedhere'].includes(name))continue;
  if(name==='label'){i=argument(s,i).end;continue;}
  if(['emph','textit','textbf'].includes(name)){const a=argument(s,i);i=a.end;const tag=name==='textbf'?'strong':'em';result+=`<${tag}>${prose(a.value)}</${tag}>`;continue;}
  if(name==='href'){const url=argument(s,i);i=url.end;const label=argument(s,i);i=label.end;if(!/^https:\/\//.test(url.value))throw Error('Non-HTTPS source link');result+=`<a href="${escape(url.value)}" target="_blank" rel="noopener">${prose(label.value)}</a>`;continue;}
  if(name==='ref'||name==='eqref'){const a=argument(s,i);i=a.end;const r=ref(a.value);result+=`<a class="internal-reference" href="#${escape(r.target)}">${name==='eqref'?'('+escape(r.number)+')':escape(r.number)}</a>`;continue;}
  if(name==='cite'){let location='';if(s[i]==='['){const end=s.indexOf(']',i);if(end<0)throw Error('Unclosed citation locator');location=s.slice(i+1,end);i=end+1;}const a=argument(s,i);i=a.end;const links=a.value.split(',').map(key=>{const item=bib.get(key.trim());if(!item)throw Error('Unknown bibliography key '+key);return `<a class="internal-reference citation" href="#bib-${escape(item.key)}">${item.number}</a>`});result+=`[${links.join(', ')}${location?', '+prose(location):''}]`;continue;}
  throw Error('Unsupported prose command '+name);
 }
 return result;
}
function content(raw){
 const tokens=[];const hold=html=>'@@WEBTOKEN'+(tokens.push(html)-1)+'@@';
 const paragraphs=value=>value.split(/\n\s*\n/).map(s=>s.trim()).filter(Boolean).map(s=>{
  let html=prose(s).trim();if(!html)return '';
  if(/^@@WEBTOKEN\d+@@$/.test(html)&&/^<(div|ul)\b/.test(tokens[Number(html.match(/\d+/)[0])]))return tokens[Number(html.match(/\d+/)[0])];
  html=html.replace(/@@WEBTOKEN(\d+)@@/g,(_,i)=>tokens[Number(i)]);
  return `<p>${html}</p>`;
 }).join('\n');
 raw=raw.replace(/\\setlength\{[^{}]*\}\{[^{}]*\}/g,'');
 raw=raw.replace(/\\begin\{equation\}([\s\S]*?)\\end\{equation\}|\\\[([\s\S]*?)\\\]|\$([^$]+)\$/g,(whole,eq,display,inline)=>{
  if(eq!==undefined){const n=equations.get(whole);return '\n\n'+hold(`<div class="numbered-equation" id="${n.id}">${math(eq,true)}<span class="equation-number" aria-label="Equation ${n.number}">(${n.number})</span></div>`)+ '\n\n';}
  if(display!==undefined)return '\n\n'+hold(`<div class="display-equation">${math(display,true)}</div>`)+'\n\n';
  return hold(math(inline,false));
 });
 raw=raw.replace(/\\begin\{itemize\}([\s\S]*?)\\end\{itemize\}/g,(_,items)=>{
  const entries=items.split(/\\item\b/);if(entries.shift().trim())throw Error('Unexpected text before first list item');
  return '\n\n'+hold(`<ul class="setup-list">${entries.map(item=>`<li>${paragraphs(item)}</li>`).join('')}</ul>`)+'\n\n';
 });
 return paragraphs(raw);
}
const inlineContent=raw=>content(raw).replace(/^<p>|<\/p>$/g,'');

function tangentDiagram(){
 const curves=[-.65,-.3,0,.3,.65].map(lambda=>{const points=Array.from({length:81},(_,i)=>{const v=-2+i/20;return `${(180-45*lambda*v*v).toFixed(2)},${(150-55*v).toFixed(2)}`});return `<polyline class="tangent-member" data-lambda="${lambda}" points="${points.join(' ')}" fill="none" stroke="${lambda<0?'#7c9478':'#a8b69c'}" stroke-width="2"/>`}).join('');
 return `<figure class="tangent-diagram" aria-labelledby="tangent-title"><h3 id="tangent-title">First-order image: rank 1</h3><p class="tangent-formula">a + bu + cv² → a + bu</p><svg viewBox="0 0 360 300" role="img" aria-labelledby="tangent-svg-title tangent-svg-desc"><title id="tangent-svg-title">Smooth curves with one shared tangent line</title><desc id="tangent-svg-desc">Five smooth members u plus lambda v squared equals zero meet at x with tangent u equals zero. The horizontal u direction is separated; the vertical v direction is invisible to their first derivatives.</desc><defs><marker id="tangent-green-arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0 0 10 5 0 10Z" fill="#456844"/></marker><marker id="tangent-rust-arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0 0 10 5 0 10Z" fill="#a06852"/></marker></defs><rect x="12" y="12" width="336" height="276" rx="16" fill="#e8ece2"/><path d="M28 150H332M180 28V272" stroke="#c4cdbd" stroke-width="1"/>${curves}<path d="M180 35V265" stroke="#4d624b" stroke-dasharray="5 5" stroke-width="1.5"/><path d="M180 150H270" stroke="#456844" stroke-width="3" marker-end="url(#tangent-green-arrow)"/><path d="M180 150V78" stroke="#a06852" stroke-width="3" marker-end="url(#tangent-rust-arrow)"/><circle cx="180" cy="150" r="4" fill="#263f2c"/><g fill="#344d35" font-size="16" font-family="Georgia,serif"><text x="330" y="171">u</text><text x="193" y="32">v</text><text x="164" y="174">x</text><text x="243" y="136">∂u</text><text x="193" y="83" fill="#a06852">∂v</text><text x="190" y="263">u = 0</text></g></svg><div class="tangent-legend"><span><i class="tangent-direction green" aria-hidden="true">→</i> ∂u: separated</span><span><i class="tangent-direction rust" aria-hidden="true">↑</i> ∂v: not separated</span></div><figcaption>Smooth members through x share the tangent u = 0. Real-slice schematic of C²; this is the subsystem Λ, not the complete |2H|.</figcaption></figure>`;
}

function render(b){
 if(b.type==='section')return `<h2 id="${b.id}">${b.number?`<span>${b.number}.</span>`:''} ${inlineContent(b.title)}</h2>`;
 if(b.type==='subsection')return `<h3 class="note-subsection" id="${b.id}">${b.number}. ${inlineContent(b.title)}</h3>`;
 if(b.type==='text'){
  if(b.content.includes('For a concrete one-dimensional image')){const cut=b.content.indexOf('Here $');if(cut<0)throw Error('Missing stalk paragraph after tangent example');return `<div class="note-prose">${content(b.content.slice(0,cut))}</div>${tangentDiagram()}<div class="note-prose">${content(b.content.slice(cut))}</div>`;}
  return `<div class="note-prose">${content(b.content)}</div>`;
 }
 if(b.type==='thebibliography')return `<section class="note-references" id="references"><h2>References</h2><ol>${b.items.map(item=>`<li id="bib-${escape(item.key)}">${content(item.content)}</li>`).join('')}</ol></section>`;
 if(b.type==='example')return `<section class="example" id="${b.id}"><h3>Example ${b.number}.${b.title?' '+inlineContent(b.title):''}</h3><div class="example-purpose">${content(b.content)}</div></section>`;
 if(b.type==='explanation')return `<details class="proof example-explanation" id="${b.id}"><summary id="explanation-toggle-${b.number}" aria-controls="explanation-body-${b.number}" aria-expanded="false"><span class="proof-heading">Explanation</span><span class="proof-icon" aria-hidden="true"></span></summary><div class="proof-body" id="explanation-body-${b.number}" role="region" aria-labelledby="explanation-toggle-${b.number}">${content(b.content)}</div></details>`;
 if(b.type==='proof'){
  const title=b.completionHeading?escape(b.completionHeading):b.title?inlineContent(b.title):'Proof';
  const introduction=b.introduction?`<div class="framework-proof"><p class="framework-proof-heading">Proof.</p>${b.introduction.map(render).join('\n')}</div>`:'';
  return introduction+`<details class="proof" id="${b.id}"><summary id="proof-toggle-${b.number}" aria-controls="proof-body-${b.number}" aria-expanded="false"><span class="proof-heading">${title}</span><span class="proof-icon" aria-hidden="true"></span></summary><div class="proof-body" id="proof-body-${b.number}" role="region" aria-labelledby="proof-toggle-${b.number}">${content(b.content)}<span class="qed" aria-label="End of proof">□</span></div></details>`;
 }
 const name=b.type[0].toUpperCase()+b.type.slice(1);
 return `<section class="statement${b.type==='setup'?' setup-statement':''}" id="${b.id}" aria-labelledby="${b.id}-title"><h3 id="${b.id}-title">${name}${b.number?' '+b.number:''}.${b.title?' '+inlineContent(b.title):''}</h3>${content(b.content)}</section>`;
}
const htmlBlocks=d.blocks.map(render).join('\n');
const stem=d.source.replace(/\.tex$/,'');
const html=`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="theme-color" content="#f5f4ef"><title>${escape(d.title)} · Nef abundance</title><link rel="icon" href="../../assets/favicon.svg" type="image/svg+xml"><link rel="stylesheet" href="../../visuals/catalog.css?v=20261001-gallery"><link rel="stylesheet" href="../spectral/vendor/katex.min.css"><link rel="stylesheet" href="note.css?v=3"><link rel="stylesheet" href="threefold.css?v=2"><link rel="stylesheet" href="jets.css?v=1"></head><body><main class="study-note"><header class="note-header"><a href="./" class="back-link">← Nef abundance</a><h1>${escape(d.title)}</h1><p class="note-date">${escape(d.date)}</p></header><article class="note-content">${htmlBlocks}</article></main><script src="../spectral/vendor/katex.min.js" defer></script><script src="jets.js?v=1" defer></script></body></html>`;
await writeFile(new URL('jets.html',root),html);
console.log(JSON.stringify({structure:d.structure,equations:equation,references:refs.size,bibliography:bib.size,sourceSha256:d.sourceSha256}));
