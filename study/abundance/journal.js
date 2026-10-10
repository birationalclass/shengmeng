// Render math without changing the original prose.
if(window.katex){
 for(const host of document.querySelectorAll('.theorem-body,.record-part li')){
  const text=host.textContent,pattern=/\$([^$]+)\$|\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)/g;
  let end=0,match;const frag=document.createDocumentFragment();
  while((match=pattern.exec(text))){frag.append(document.createTextNode(text.slice(end,match.index)));const span=document.createElement('span');katex.render(match[1]??match[2]??match[3],span,{displayMode:match[2]!==undefined,throwOnError:false,macros:{'\\Q':'\\mathbb{Q}'}});frag.append(span);end=pattern.lastIndex;}
  frag.append(document.createTextNode(text.slice(end)));host.replaceChildren(frag);
 }
}
