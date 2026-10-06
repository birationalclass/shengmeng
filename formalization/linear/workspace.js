import {t} from './i18n.js?v=20261006-linear-3';
export function installWorkspace() {
  const dialog=document.createElement('dialog');dialog.className='reading-dialog';dialog.setAttribute('aria-labelledby','readingTitle');dialog.innerHTML=`<div class="reading-heading"><h2 id="readingTitle"></h2><button class="button small" id="closeReading">${t('关闭')} · Esc</button></div>`;
  const original=document.querySelector('#original'),evidence=document.querySelector('#evidence');dialog.append(original,evidence);document.body.append(dialog);
  function setModule(id){document.querySelectorAll('.module-navigation a').forEach(a=>{if(a.hash==='#'+id)a.setAttribute('aria-current','page');else a.removeAttribute('aria-current');});}
  dialog.addEventListener('close',()=>setModule('atlas'));
  function open(target){setModule(target==='evidence'?'evidence':'original');const proof=target==='original'||target.startsWith('paper-');original.hidden=!proof;evidence.hidden=proof;dialog.querySelector('h2').textContent=t(proof?'原始证明':'验证记录');if(!dialog.open)dialog.showModal();requestAnimationFrame(()=>{if(target.startsWith('paper-'))document.getElementById(target)?.scrollIntoView({block:'start'});else dialog.scrollTop=0;});}
  document.querySelector('#closeReading').onclick=()=>dialog.close();dialog.addEventListener('click',e=>{if(e.target===dialog){const r=dialog.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)dialog.close();}});
  document.addEventListener('click',e=>{const a=e.target.closest('a[href^="#"]');if(a){const id=a.getAttribute('href').slice(1);if(['original','evidence'].includes(id)||id.startsWith('paper-')){e.preventDefault();open(id);}else if(id==='atlas'){e.preventDefault();if(dialog.open)dialog.close();}}if(e.target.closest('[data-select]')&&dialog.open)dialog.close();},true);
  const toggle=document.createElement('button');toggle.className='button small inspector-toggle';toggle.textContent=t('详情');toggle.setAttribute('aria-pressed','false');document.querySelector('.graph-toolbar').append(toggle);toggle.onclick=()=>{const shown=document.body.classList.toggle('inspector-open');toggle.setAttribute('aria-pressed',String(shown));};
  const target=location.hash.slice(1);if(['original','evidence'].includes(target)||target.startsWith('paper-'))open(target);
  const resize=new ResizeObserver(()=>{if(innerWidth>760)document.body.classList.remove('inspector-open');});resize.observe(document.body);
}
