// Run with node scripts/render-publications.mjs after updating publications.json.
// The complete list is rendered into HTML so it also works without JavaScript.
import { readFileSync, writeFileSync } from 'node:fs';
const root = new URL('../', import.meta.url);
const { papers } = JSON.parse(readFileSync(new URL('publications.json', root), 'utf8'));
const escape = text => String(text).replace(/[&<>\"]/g, char => ({'&':'&amp;','<':'&lt;','>':'&gt;','\"':'&quot;'}[char]));
if (new Set(papers.map(p => p.arxiv)).size !== papers.length) throw new Error('Duplicate paper');
for (const paper of papers) {
  if (!paper.authors.includes('Sheng Meng') || !paper.url.startsWith('https://arxiv.org/abs/')) throw new Error('Invalid paper');
}
papers.sort((a,b) => b.year-a.year || b.arxiv.localeCompare(a.arxiv));
const rows = papers.map(p => `          <li class="publication-row">
            <span class="paper-year">${p.year}</span>
            <div class="paper-content"><h3>${escape(p.title)}</h3><p class="paper-authors">${p.authors.map(escape).join(' · ')}</p><p class="paper-venue">${p.publication ? escape(p.publication) : '<span data-i18n="preprint">Preprint</span>'}</p></div>
            <a class="paper-link" href="${escape(p.url)}" target="_blank" rel="noreferrer" aria-label="Link: ${escape(p.title)}">Link<span aria-hidden="true"> ↗</span></a>
          </li>`).join('\n');
const path = new URL('index.html', root);
let html = readFileSync(path, 'utf8');
const pattern = /<!-- publications:start -->[\s\S]*?<!-- publications:end -->/;
if (!pattern.test(html)) throw new Error('Missing publication markers');
html = html.replace(pattern, `<!-- publications:start -->\n        <ol class="publication-list complete-paper-list">\n${rows}\n        </ol>\n        <!-- publications:end -->`);
html = html.replace(/(<b id="paperCount">)\d+(<\/b>)/, `$1${papers.length}$2`);
writeFileSync(path, html);
console.log(`Rendered ${papers.length} papers (${papers.filter(p=>p.publication).length} published, ${papers.filter(p=>!p.publication).length} preprints).`);
