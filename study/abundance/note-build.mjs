import {readFile,writeFile} from 'node:fs/promises';
const root=new URL('./',import.meta.url);
const d=JSON.parse(await readFile(new URL('note-content.json',root),'utf8'));
const escape=s=>s.replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function prose(s){
 s=s.replace(/\\(?:smallskip|noindent)\b/g,'').trim();
 // Protect math before converting prose typography and inline emphasis.
 const math=[];s=s.replace(/\$[^$]+\$|\\\[[\s\S]*?\\\]/g,x=>'@@MATH'+(math.push(x)-1)+'@@');
 const links=[];s=s.replace(/\\href\{(https:\/\/[^{}]+)\}\{((?:\\emph\{[^{}]*\}|[^{}])+)\}/g,(_,url,label)=>{
  const approved='https://github.com/openai/math/blob/main/preprints/Numerical-Semiampleness-of-Nef-Adjoint-Divisors-October-3-2026/paper.pdf';
  if(url!==approved)throw Error('Unapproved note hyperlink');
  const text=escape(label.replace(/\s+/g,' ')).replace(/\\emph\{([^{}]*)\}/g,'<em>$1</em>');
  links.push(`<a href="${escape(url)}" target="_blank" rel="noopener">${text}</a>`);
  return '@@LINK'+(links.length-1)+'@@';
 });
 s=s.replace(/\\'\{e\}/g,'é');
 s=escape(s.replace(/\s+/g,' ')).replace(/\\(?:emph|textit)\{([^{}]*)\}/g,'<em>$1</em>').replace(/``/g,'“').replace(/&#39;&#39;/g,'”').replace(/--/g,'–');
 s=s.replace(/@@MATH(\d+)@@/g,(_,i)=>escape(math[Number(i)]));
 s=s.replace(/@@LINK(\d+)@@/g,(_,i)=>links[Number(i)]);
 return s;
}
const paragraphs=s=>s.split(/\n\s*\n/).map(prose).filter(Boolean).map(x=>`<p>${x}</p>`).join('\n');
let sec=0;
const content=d.blocks.map(b=>{
 if(b.type==='section')return `<h2 id="section-${++sec}"><span>${sec}.</span> ${escape(sec===1?'Verified Lemmas':b.title)}</h2>`;
 if(b.type==='text')return `<div class="note-prose">${paragraphs(b.content)}</div>`;
 if(b.type==='proof')return `<details class="proof"><summary id="proof-toggle-${b.number}" aria-controls="proof-body-${b.number}" aria-expanded="false"><span class="proof-heading">Proof${sec===1?' <span class="proof-verification"><span aria-hidden="true">✓</span> verified by Sheng</span>':''}</span><span class="proof-icon" aria-hidden="true"></span></summary><div class="proof-body" id="proof-body-${b.number}" role="region" aria-labelledby="proof-toggle-${b.number}">${paragraphs(b.content)}<span class="qed" aria-label="End of proof">□</span></div></details>`;
 return `<section class="statement" id="${b.type}-${b.number}" aria-labelledby="statement-title-${b.number}"><h3 id="statement-title-${b.number}">${b.type[0].toUpperCase()+b.type.slice(1)} ${b.number}.</h3>${b.type==='proposition'&&b.number==='2.2'?'<p class="statement-status">Source assertion · proof not supplied or audited here.</p>':''}${paragraphs(b.content)}</section>`;
}).join('\n');
const html=`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="theme-color" content="#f5f4ef"><title>${escape(d.title)} · Nef abundance</title><link rel="icon" href="../../assets/favicon.svg" type="image/svg+xml"><link rel="stylesheet" href="../../visuals/catalog.css?v=20261001-gallery"><link rel="stylesheet" href="../spectral/vendor/katex.min.css"><link rel="stylesheet" href="note.css?v=3"></head><body><main class="study-note"><header class="note-header"><a href="./" class="back-link">← Nef abundance</a><h1>${escape(d.title)}</h1><p class="note-date">${escape(d.date)}</p></header><article class="note-content">${content}</article></main><script src="../spectral/vendor/katex.min.js" defer></script><script src="note.js?v=1" defer></script></body></html>`;
await writeFile(new URL('note.html',root),html);console.log(`Built complete note: ${d.blocks.length} blocks`);
