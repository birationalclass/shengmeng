// Counts describe the exported source snapshot, never verification status.
import {buildSourcePacks} from './source-pack-catalog.js?v=20261006-linear-8';
let dispose = () => {};
export function installLeanLineCounts({snapshot, nodes}) {
  dispose();
  if (!document.querySelector('link[data-lean-line-styles]')) {
    const css = document.createElement('link');
    css.rel = 'stylesheet';
    css.href = new URL('line-counts.css?v=20261006-linear-8', import.meta.url).href;
    css.dataset.leanLineStyles = '';
    document.head.append(css);
  }
  const files = new Map(snapshot.files.filter(f => f.path.endsWith('.lean')).map(f => [f.path, f]));
  const complete = [...files.values()].every(f => Number.isInteger(f.lineCount));
  const total = complete ? [...files.values()].reduce((sum, f) => sum + f.lineCount, 0) : null;
  const nodeFiles = new Map(nodes.map(node => {
    const declaration = node.decl && snapshot.declarations[node.decl];
    const file = files.get(declaration?.path || node.file);
    return [node.id, node.id==='lemma' ? [...files.values()] : file ? [file] : []];
  }));
  const packFiles = new Map(buildSourcePacks(nodes).map(pack => {
    const unique = new Map(pack.cards.flatMap(node => nodeFiles.get(node.id)).map(file => [file.path, file]));
    return [pack.id, {files:[...unique.values()], complete:pack.cards.every(node => nodeFiles.get(node.id).length)}];
  }));
  const legend = document.querySelector('.refuge-identity');
  let summary = legend.querySelector('.lean-source-total');
  if (!summary) { summary = document.createElement('span'); summary.className = 'lean-source-total'; legend.querySelector('h1').after(summary); }
  summary.dataset.leanTotalLines = total === null ? '' : String(total);
  const render = () => {
    const english = document.documentElement.lang.startsWith('en');
    const number = n => n.toLocaleString(english ? 'en-US' : 'zh-CN');
    const rule = english
      ? 'Physical lines, including comments and blank lines. Exported project .lean files only, including the audit script; excludes mathlib. Each file is counted once in the total. Card counts cover their source module, including definitions and helper lemmas, without dependency modules.'
      : '按物理行统计，包含注释与空行。仅计公开工程的 .lean 文件（含公理检查脚本），不含 mathlib；总数对文件去重。卡片显示对应源码模块（含定义与辅助引理）的行数，不含依赖模块。';
    const packRule = english
      ? 'Pack total: physical lines (including comments and blank lines) in source modules linked to its member cards, counted once per file; excludes dependency modules.'
      : '卡包总数：包内卡片关联的源码模块物理行（含注释与空行），按文件去重，不含依赖模块。';
    summary.textContent = total === null ? (english ? 'Lean lines unavailable' : 'Lean 行数未提供') : (english ? `Lean · ${number(total)} lines` : `Lean · ${number(total)} 行`);
    summary.title = rule;
    summary.setAttribute('aria-label', summary.textContent + '. ' + rule);
    // Resolve the current DOM after every world render: deck and gold cards are replaced on navigation.
    for (const card of document.querySelectorAll('#graph .node[data-node], .proof-worlds .node[data-world-node], .proof-worlds .node[data-world-pack], .theorem-target-card')) {
      const pack = card.dataset.worldPack && packFiles.get(card.dataset.worldPack);
      const sourceFiles = pack ? pack.files : nodeFiles.get(card.dataset.worldNode || card.dataset.node || card.dataset.targetNode) || [];
      const hasCount = sourceFiles.length > 0 && (!pack || pack.complete) && sourceFiles.every(file => Number.isInteger(file.lineCount));
      const count = hasCount ? sourceFiles.reduce((sum, file) => sum + file.lineCount, 0) : null;
      let badge = card.querySelector(':scope > .node-lean-lines');
      if (!badge) { badge = document.createElement('span'); badge.className = 'node-lean-lines'; card.append(badge); }
      badge.dataset.leanFile = !pack && sourceFiles[0] ? sourceFiles[0].path : '';
      badge.dataset.leanFiles = JSON.stringify(sourceFiles.map(file => file.path));
      badge.dataset.leanLines = hasCount ? String(count) : '';
      badge.textContent = hasCount ? (english ? `Lean ${number(count)} lines` : `Lean ${number(count)} 行`) : (english ? 'Lean lines unavailable' : 'Lean 行数未提供');
      badge.title = hasCount ? `${sourceFiles.map(file => file.path).join('\n')}\n${pack ? packRule : rule}` : (english ? 'Source line-count metadata is unavailable for this card; this does not describe proof verification.' : '本卡的源码行数元数据未提供；这不表示证明未通过验证。');
      badge.setAttribute('aria-label', badge.textContent + '. ' + (pack ? packRule : rule));
    }
  };
  render();
  window.addEventListener('languagechange', render);
  document.addEventListener('proofworldrender', render);
  document.addEventListener('theoremcardchange', render, true);
  dispose = () => {
    window.removeEventListener('languagechange', render);
    document.removeEventListener('proofworldrender', render);
    document.removeEventListener('theoremcardchange', render, true);
  };
}
