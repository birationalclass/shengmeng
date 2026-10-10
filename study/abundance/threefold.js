const macros={'\\Q':'\\mathbb{Q}','\\C':'\\mathbb{C}','\\OO':'\\mathcal{O}','\\mult':'\\operatorname{mult}','\\nef':'\\operatorname{n}'};
if(window.katex)for(const host of document.querySelectorAll('[data-math]')){
 katex.render(host.dataset.math,host,{displayMode:host.dataset.display==='true',throwOnError:false,macros,trust:context=>context.command==='\\href'&&context.url.startsWith('#')});
}
for(const proof of document.querySelectorAll('details.proof'))proof.addEventListener('toggle',()=>proof.querySelector('summary').setAttribute('aria-expanded',String(proof.open)));
function revealReference(hash){
 if(!hash||hash==='#')return;
 const target=document.getElementById(decodeURIComponent(hash.slice(1)));if(!target)return;
 for(let parent=target;parent;parent=parent.parentElement)if(parent.matches('details.proof')){parent.open=true;parent.querySelector('summary').setAttribute('aria-expanded','true');}
 requestAnimationFrame(()=>target.scrollIntoView({block:'start',behavior:'instant'}));
}
document.addEventListener('click',event=>{const link=event.target.closest('a[href^="#"]');if(link&&link.hash)revealReference(link.hash);});
window.addEventListener('hashchange',()=>revealReference(location.hash));
if(location.hash)revealReference(location.hash);
