// Counts describe the exported source snapshot, never verification status.
let dispose = () => {};
export function installLeanLineCounts({snapshot, nodes}) {
  dispose();
  if (!document.querySelector('link[data-lean-line-styles]')) {
    const css = document.createElement('link');
    css.rel = 'stylesheet';
    css.href = new URL('line-counts.css?v=20261003-lines-1', import.meta.url).href;
    css.dataset.leanLineStyles = '';
    document.head.append(css);
  }
  const files = new Map(snapshot.files.filter(f => f.path.endsWith('.lean')).map(f => [f.path, f]));
  const complete = [...files.values()].every(f => Number.isInteger(f.lineCount));
  const total = complete ? [...files.values()].reduce((sum, f) => sum + f.lineCount, 0) : null;
  const badges = nodes.map(node => {
    const card = document.querySelector(`#graph .node[data-node="${node.id}"]`);
    if (!card) return null;
    let badge = card.querySelector('.node-lean-lines');
    if (!badge) { badge = document.createElement('span'); badge.className = 'node-lean-lines'; card.append(badge); }
    const declaration = node.decl && snapshot.declarations[node.decl];
    const file = declaration && files.get(declaration.path);
    badge.dataset.leanFile = file?.path || '';
    return {badge, file};
  }).filter(Boolean);
  const legend = document.querySelector('.atlas-statusbar .legend');
  let summary = legend.querySelector('.lean-source-total');
  if (!summary) { summary = document.createElement('span'); summary.className = 'lean-source-total'; legend.append(summary); }
  summary.dataset.leanTotalLines = total === null ? '' : String(total);
  const render = () => {
    const english = document.documentElement.lang.startsWith('en');
    const number = n => n.toLocaleString(english ? 'en-US' : 'zh-CN');
    const rule = english
      ? 'Physical lines, including comments and blank lines. Exported project .lean files only, including the audit script; excludes mathlib. Each file is counted once in the total. Card counts cover their source module, including definitions and helper lemmas, without dependency modules.'
      : '按物理行统计，包含注释与空行。仅计公开工程的 .lean 文件（含公理检查脚本），不含 mathlib；总数对文件去重。卡片显示对应源码模块（含定义与辅助引理）的行数，不含依赖模块。';
    summary.textContent = total === null ? (english ? 'Lean lines unavailable' : 'Lean 行数未提供') : (english ? `Lean · ${number(total)} lines` : `Lean · ${number(total)} 行`);
    summary.title = rule;
    summary.setAttribute('aria-label', summary.textContent + '. ' + rule);
    for (const {badge, file} of badges) {
      const hasCount = Number.isInteger(file?.lineCount);
      badge.textContent = hasCount ? (english ? `Lean ${number(file.lineCount)} lines` : `Lean ${number(file.lineCount)} 行`) : (english ? 'Lean not implemented' : 'Lean 未实现');
      badge.title = hasCount ? `${file.path}\n${rule}` : (english ? 'No implemented declaration is linked to this card in the published snapshot.' : '公开快照中，本卡尚未关联已实现的 Lean 声明。');
      badge.dataset.leanLines = hasCount ? String(file.lineCount) : '';
    }
  };
  render();
  window.addEventListener('languagechange', render);
  dispose = () => window.removeEventListener('languagechange', render);
}
