import {escapeHTML} from './theorem-statements.js?v=20261008-nagata-3';
export function installLeanCatalog({nodes,audit,complete,worlds,select}){
 const en=()=>document.documentElement.lang.startsWith('en'),text=(zh,eng)=>en()?eng:zh;
 const dialog=document.createElement('dialog');dialog.className='lean-catalog';document.body.append(dialog);
 const all=new Map(nodes.map(n=>[n.id,n]));let term='',scope='target',file='',generated=false,page=0;
 const files=[...new Set(nodes.map(n=>n.file))].sort();
 function render(){
  const allowed=scope==='all'?null:worlds.model.closure(worlds.state.target),q=term.toLowerCase();
  const pool=nodes.filter(n=>(!allowed||allowed.has(n.id))&&(!file||n.file===file)&&(generated||!n.generated)&&(!q||(n.decl+' '+n.formalType).toLowerCase().includes(q)));
  const pages=Math.max(1,Math.ceil(pool.length/30));page=Math.min(page,pages-1);const shown=pool.slice(page*30,(page+1)*30);
  dialog.innerHTML=`<header><h2>${text('完整 Lean 证明库','Complete Lean proof library')}</h2><button data-close aria-label="${text('关闭','Close')}">×</button></header><p class="lean-coverage">${text('全部项目','Whole project')}: ${complete.summary.constants} ${text('常量','constants')} · ${text('最终定理实际依赖','Main theorem dependencies')}: ${complete.summary.mainConstants} · ${text('独立源码文件','Source files')}: ${complete.summary.sourceFiles}. ${text('编译器辅助项保留；mathlib 引用另列，不计入项目源码。','Compiler-generated auxiliaries are retained; mathlib references are separate and excluded from project source counts.')}</p><div class="lean-search"><input data-search value="${escapeHTML(term)}" placeholder="${text('搜索声明、参数或结论','Search declarations, inputs or conclusions')}" aria-label="${text('搜索 Lean 声明','Search Lean declarations')}"><select data-scope aria-label="${text('检索范围','Search scope')}"><option value="target" ${scope==='target'?'selected':''}>${text('当前目标的完整依赖','Complete dependencies of current goal')}</option><option value="all" ${scope==='all'?'selected':''}>${text('全工程，包括未被主定理使用的声明','Whole project, including unused declarations')}</option></select><select data-file aria-label="${text('源码文件','Source file')}"><option value="">${text('全部文件','All files')}</option>${files.map(f=>`<option value="${escapeHTML(f)}" ${file===f?'selected':''}>${escapeHTML(f.split('/').pop())}</option>`).join('')}</select><label><input type="checkbox" data-generated ${generated?'checked':''}>${text('显示编译器辅助项','Show compiler-generated auxiliaries')}</label></div><p>${pool.length} ${text('个匹配声明','matching declarations')} · ${text('第','Page')} ${page+1}/${pages}</p><div class="lean-records">${shown.map(n=>`<button data-open="${escapeHTML(n.id)}"><b>${escapeHTML(n.decl)}</b><span>${escapeHTML(n.leanKind)} · ${escapeHTML(n.file.split('/').pop())} · ${n.deps.length} ${text('个直接项目依赖','direct project dependencies')} · ${n.externalDependencies.length} ${text('个外部引用','external references')}</span><small>${escapeHTML(n.formalType.slice(0,320))}</small></button>`).join('')}</div><footer><button data-prev ${page?'':'disabled'}>←</button><span>${page+1}/${pages}</span><button data-next ${page+1<pages?'':'disabled'}>→</button></footer>`;
  dialog.querySelector('[data-close]').onclick=()=>dialog.close();
  dialog.querySelector('[data-search]').oninput=e=>{term=e.target.value;page=0;const cursor=e.target.selectionStart;render();const input=dialog.querySelector('[data-search]');input.focus();input.setSelectionRange(cursor,cursor);};
  dialog.querySelector('[data-scope]').onchange=e=>{scope=e.target.value;page=0;render();};
  dialog.querySelector('[data-file]').onchange=e=>{file=e.target.value;page=0;render();};
  dialog.querySelector('[data-generated]').onchange=e=>{generated=e.target.checked;page=0;render();};
  dialog.querySelector('[data-prev]').onclick=()=>{page--;render();};dialog.querySelector('[data-next]').onclick=()=>{page++;render();};
  dialog.querySelectorAll('[data-open]').forEach(b=>b.onclick=async()=>{dialog.close();await worlds.enter(b.dataset.open);select(b.dataset.open);});
 }
 const coverage=document.createElement('div');coverage.className='lean-proof-coverage';document.querySelector('.proof-world-tools').prepend(coverage);
 function labels(){coverage.textContent=text('完整主证明：','Complete main proof: ')+complete.summary.mainConstants+text(' 个常量 · ',' constants · ')+complete.summary.mainSourceFiles+text(' 个文件',' files');coverage.title=text('全部真实项目依赖均可逐层展开；含编译器辅助声明。','Every actual project dependency can be expanded, including compiler-generated auxiliaries.');}
 labels();window.addEventListener('languagechange',()=>{labels();if(dialog.open)render();});
 document.addEventListener('leancatalogrequest',()=>{page=0;render();dialog.showModal();});
 window.nagataUI.catalog={open(){document.dispatchEvent(new Event('leancatalogrequest'));},dialog};
}
