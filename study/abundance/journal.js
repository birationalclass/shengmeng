const entries=[...document.querySelectorAll('.journal-record')];
const search=document.querySelector('#journalSearch'),buttons=[...document.querySelectorAll('[data-filter]')];
let filter='all';
function update(){const q=search.value.trim().toLocaleLowerCase();let count=0;for(const entry of entries){const match=filter==='all'||(filter==='pending'?entry.dataset.pending==='true':entry.dataset.verified==='true');entry.hidden=!(match&&entry.textContent.toLocaleLowerCase().includes(q));if(!entry.hidden)count++;}document.querySelector('#recordCount').textContent=count+' 条记录';document.querySelector('#journalEmpty').hidden=count!==0;}
search.addEventListener('input',update);buttons.forEach(button=>button.addEventListener('click',()=>{filter=button.dataset.filter;buttons.forEach(b=>b.setAttribute('aria-pressed',String(b===button)));update();}));

// Render math without changing the original prose.
if(window.katex){
 for(const host of document.querySelectorAll('.theorem-body,.record-part li')){
  const text=host.textContent,pattern=/\$([^$]+)\$|\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)/g;
  let end=0,match;const frag=document.createDocumentFragment();
  while((match=pattern.exec(text))){frag.append(document.createTextNode(text.slice(end,match.index)));const span=document.createElement('span');katex.render(match[1]??match[2]??match[3],span,{displayMode:match[2]!==undefined,throwOnError:false,macros:{'\\Q':'\\mathbb{Q}'}});frag.append(span);end=pattern.lastIndex;}
  frag.append(document.createTextNode(text.slice(end)));host.replaceChildren(frag);
 }
}
