const macros={'\\Q':'\\mathbb{Q}','\\C':'\\mathbb{C}','\\OO':'\\mathcal{O}','\\ord':'\\operatorname{ord}','\\mult':'\\operatorname{mult}','\\nef':'\\operatorname{n}'};
if(window.katex) for(const host of document.querySelectorAll('.note-content p')){
 const pattern=/\$([^$]+)\$|\\\[([\s\S]*?)\\\]/g;
 const walker=document.createTreeWalker(host,NodeFilter.SHOW_TEXT);const nodes=[];while(walker.nextNode())nodes.push(walker.currentNode);
 for(const node of nodes){const text=node.textContent;let end=0,m;const frag=document.createDocumentFragment();pattern.lastIndex=0;
 while((m=pattern.exec(text))){frag.append(document.createTextNode(text.slice(end,m.index)));const span=document.createElement('span');katex.render(m[1]??m[2],span,{displayMode:m[2]!==undefined,throwOnError:false,macros});frag.append(span);end=pattern.lastIndex;}
 if(end){frag.append(document.createTextNode(text.slice(end)));node.replaceWith(frag);}
 }
}
for(const proof of document.querySelectorAll('.proof'))proof.addEventListener('toggle',()=>proof.querySelector('summary').setAttribute('aria-expanded',String(proof.open)));
