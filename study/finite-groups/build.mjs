import {readFile, writeFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {runInNewContext} from 'node:vm';

const root = new URL('./', import.meta.url);
const sandbox = {module: {exports: {}}, exports: {}};
runInNewContext(await readFile(new URL('../spectral/vendor/katex.min.js', root), 'utf8'), sandbox);
const katex = sandbox.module.exports;
const data = JSON.parse(await readFile(new URL('content.json', root), 'utf8'));
const pageTitle = '有胆就下一百层';
const groups = JSON.parse(await readFile(new URL('groups.json', root), 'utf8'));
const source = await readFile(new URL(data.source, root));
if (createHash('sha256').update(source).digest('hex') !== data.sourceSha256) throw Error('Re-extract the current lecture');
if (groups.length !== 1048) throw Error('Incomplete group catalogue');
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const macros = {'\\Aut':'\\operatorname{Aut}', '\\GL':'\\operatorname{GL}', '\\ord':'\\operatorname{ord}', '\\Z':'\\mathrm Z'};
let formulaCount = 0;
function math(tex, display = false) {
  formulaCount++;
  return katex.renderToString(tex.trim(), {displayMode: display, throwOnError: true, strict: 'ignore', macros, output: 'htmlAndMathml'});
}
function argument(s, start) {
  if (s[start] !== '{') throw Error('Expected argument: ' + s.slice(start, start + 80));
  let depth = 1;
  for (let i = start + 1; i < s.length; i++) {
    if (s[i - 1] === '\\') continue;
    if (s[i] === '{') depth++;
    if (s[i] === '}' && !--depth) return {value: s.slice(start + 1, i), end: i + 1};
  }
  throw Error('Unclosed argument');
}
function prose(s) {
  let result = '', i = 0;
  while (i < s.length) {
    if (s[i] !== '\\') {
      let end = s.indexOf('\\', i); if (end < 0) end = s.length;
      result += esc(s.slice(i, end).replace(/~/g, ' ').replace(/\s+/g, ' ')); i = end; continue;
    }
    const command = /^\\([a-zA-Z]+)/.exec(s.slice(i));
    if (!command) throw Error('Unsupported escape: ' + s.slice(i, i + 80));
    const name = command[1]; i += command[0].length;
    if (['noindent', 'clearpage'].includes(name)) continue;
    if (name === 'quad') { result += ' '; continue; }
    if (name === 'label') { i = argument(s, i).end; continue; }
    if (name === 'addcontentsline') { for (let j = 0; j < 3; j++) i = argument(s, i).end; continue; }
    if (['textbf', 'emph', 'textit', 'texttt'].includes(name)) {
      const a = argument(s, i); i = a.end;
      const tag = name === 'textbf' ? 'strong' : name === 'texttt' ? 'code' : 'em';
      result += `<${tag}>${prose(a.value)}</${tag}>`; continue;
    }
    if (name === 'texorpdfstring') {
      const a = argument(s, i); i = argument(s, a.end).end; result += prose(a.value); continue;
    }
    if (name === 'url') {
      const a = argument(s, i); i = a.end;
      if (!/^https:\/\//.test(a.value)) throw Error('Unexpected URL');
      result += `<a href="${esc(a.value)}" target="_blank" rel="noopener">${esc(a.value)}</a>`; continue;
    }
    throw Error('Unsupported prose command: ' + name);
  }
  return result;
}
function content(raw) {
  const tokens = [];
  const hold = html => `@@GROUPTOKEN${tokens.push(html) - 1}@@`;
  const restore = value => {
    for (let i = 0; value.includes('@@GROUPTOKEN'); i++) {
      if (i > 20) throw Error('Recursive token');
      value = value.replace(/@@GROUPTOKEN(\d+)@@/g, (_, n) => tokens[Number(n)]);
    }
    return value;
  };
  const paragraphs = value => value.split(/\n\s*\n/).map(x => x.trim()).filter(Boolean).map(x => {
    const rendered = restore(prose(x)).trim();
    return /^<(?:div|table|ul|ol|pre)\b/.test(rendered) ? rendered : `<p>${rendered}</p>`;
  }).join('\n');
  raw = raw.replace(/\\begin\{verbatim\}([\s\S]*?)\\end\{verbatim\}/g, (_, code) => '\n\n' + hold(`<pre><code>${esc(code.trim())}</code></pre>`) + '\n\n');
  raw = raw.replace(/\\\[([\s\S]*?)\\\]|\$([^$]+)\$/g, (_, display, inline) => display !== undefined ? '\n\n' + hold(`<div class="display-equation">${math(display, true)}</div>`) + '\n\n' : hold(math(inline)));
  raw = raw.replace(/\\begin\{tabular\}\{[^{}]+\}([\s\S]*?)\\end\{tabular\}/g, (_, table) => {
    const rows = table.replace(/\\(?:toprule|midrule|bottomrule)\b/g, '').trim().split('\\\\').map(row => row.trim()).filter(Boolean);
    const html = `<div class="table-wrap"><table><thead><tr>${rows.shift().split('&').map(c => `<th scope="col">${restore(prose(c))}</th>`).join('')}</tr></thead><tbody>${rows.map(row => `<tr>${row.split('&').map(c => `<td>${restore(prose(c))}</td>`).join('')}</tr>`).join('')}</tbody></table></div>`;
    return '\n\n' + hold(html) + '\n\n';
  });
  raw = raw.replace(/\\(?:begin|end)\{center\}/g, '');
  raw = raw.replace(/\\begin\{(itemize|enumerate)\}([\s\S]*?)\\end\{\1\}/g, (_, kind, items) => {
    const entries = items.split(/\\item\b/); if (entries.shift().trim()) throw Error('Unexpected list prefix');
    const tag = kind === 'itemize' ? 'ul' : 'ol';
    return '\n\n' + hold(`<${tag}>${entries.map(item => `<li>${paragraphs(item)}</li>`).join('')}</${tag}>`) + '\n\n';
  });
  const result = paragraphs(raw);
  if (result.includes('@@GROUPTOKEN')) throw Error('Unrestored token');
  return result;
}
const inline = raw => content(raw).replace(/^<p>|<\/p>$/g, '');
const byOrder = new Map(Array.from({length:100}, (_, i) => [i + 1, groups.filter(g => g.n === i + 1)]));
const letters = 'abcdef';
const word = vector => vector.map((e,i) => !e ? '' : e === 1 ? letters[i] : `${letters[i]}^{${e}}`).join('') || '1';
function relations(g) {
  const terms = [`R=(${g.relative_orders.join(',')})`];
  g.powers.forEach((v,i) => { if (v.some(Boolean)) terms.push(`${letters[i]}^{${g.relative_orders[i]}}=${word(v)}`); });
  g.commutators.forEach(([j,k,v]) => { if (v.some(Boolean)) terms.push(`[${letters[j-1]},${letters[k-1]}]=${word(v)}`); });
  return terms.map(t => { math(t); return `<span class="math-source" data-math="${esc(t)}">${esc(t)}</span>`; }).join('; ');
}
const htmlBlocks = [];
for (const order of data.orders) {
  const n = order.n;
  const list = byOrder.get(n);
  htmlBlocks.push(`<section class="order-section" id="order-${n}"><h2>${n} 阶群</h2>`);
  if (list.length === 1) {
    const g = list[0];
    htmlBlocks.push(`<div class="note-prose" id="group-${n}-${g.i}"><p>只有一个同构类型：${math(g.labelTex)}，编号 [${n},${g.i}]。</p></div>`);
  } else {
    htmlBlocks.push(`<p>共有 ${list.length} 个同构类型，其中 ${order.abelian} 个阿贝尔。</p>`);
    htmlBlocks.push(`<div class="table-wrap order-table"><table><caption class="sr-only">${n} 阶群的全部同构类型</caption><thead><tr><th scope="col">编号</th><th scope="col">群</th><th scope="col">${math('(z,d,e)')}</th></tr></thead><tbody>${list.map(g => `<tr id="group-${n}-${g.i}"><th scope="row">[${n},${g.i}]</th><td>${math(g.labelTex)}${g.abelian ? '<span class="group-kind">阿贝尔</span>' : !g.solvable ? '<span class="group-kind">非可解</span>' : `<details class="proof presentation"><summary id="relations-toggle-${n}-${g.i}" aria-controls="relations-body-${n}-${g.i}" aria-expanded="false"><span class="proof-heading">生成关系</span><span class="proof-icon" aria-hidden="true"></span></summary><div class="proof-body group-presentation" id="relations-body-${n}-${g.i}" role="region" aria-labelledby="relations-toggle-${n}-${g.i}">${relations(g)}</div></details>`}</td><td>(${g.centre},${g.derived},${g.exponent})</td></tr>`).join('')}</tbody></table></div>`);
  }
  if (order.explanation) htmlBlocks.push(`<div class="note-prose">${content(order.explanation)}</div>`);
  if (order.proof) htmlBlocks.push(`<details class="proof theorem-proof" id="proof-${n}"><summary id="proof-toggle-${n}" aria-controls="proof-body-${n}" aria-expanded="false"><span class="proof-heading">${inline(order.proofCaption)}</span><span class="proof-icon" aria-hidden="true"></span></summary><div class="proof-body" id="proof-body-${n}" role="region" aria-labelledby="proof-toggle-${n}">${content(order.proof)}<span class="qed" aria-label="证毕">□</span></div></details>`);
  htmlBlocks.push('</section>');
}
htmlBlocks.push('<section class="notation-section" id="notation"><h2>记号与分类依据</h2>');
const noteParts = data.notes.split(/\\subsection\*\{([^{}]+)\}/);
if (noteParts.shift().trim()) throw Error('Unexpected notation preface');
for (let i = 0; i < noteParts.length; i += 2) htmlBlocks.push(`<h3 class="note-subsection">${esc(noteParts[i])}</h3>${content(noteParts[i + 1])}`);
htmlBlocks.push('</section>');
const html = `<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="description" content="从1阶群开始，逐阶列出1–100阶有限群的全部1048个同构类型，附分类证明与生成关系。"><meta name="theme-color" content="#f5f4ef"><title>${esc(pageTitle)} · Study</title><link rel="icon" href="../../assets/favicon.svg" type="image/svg+xml"><link rel="preload" href="fonts/liujianmaocao-title.ttf" as="font" type="font/ttf" crossorigin><link rel="stylesheet" href="../../visuals/catalog.css?v=20261001-gallery"><link rel="stylesheet" href="../spectral/vendor/katex.min.css"><link rel="stylesheet" href="../abundance/note.css?v=3"><link rel="stylesheet" href="groups.css?v=20261026-title"></head><body><h1 class="vertical-title">${esc(pageTitle)}</h1><main class="study-note"><header class="note-header"><a href="../" class="back-link">← Study</a><p class="note-date">${esc(data.date)}</p><p><a href="finite-groups-1-100.pdf" target="_blank" rel="noopener">PDF ↗</a></p></header><article class="note-content">${htmlBlocks.join('\n')}</article></main><script src="../spectral/vendor/katex.min.js" defer></script><script src="../abundance/note.js?v=1" defer></script><script src="groups.js?v=20261026" defer></script></body></html>`;
if (/\/Users\/|\/private\/|verified by Sheng|@@GROUPTOKEN|katex-error/.test(html)) throw Error('Unexpected public content');
await writeFile(new URL('index.html', root), html);
console.log(JSON.stringify({structure: data.structure, groups: groups.length, formulas: formulaCount, sourceSha256: data.sourceSha256, bytes: Buffer.byteLength(html)}));
