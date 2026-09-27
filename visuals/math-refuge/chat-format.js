// Only DOM text nodes and KaTeX are allowed; chat content never becomes raw HTML.
export function renderChatText(container,value){
 container.replaceChildren();const text=String(value||'').slice(0,24000),pattern=/(\$\$[\s\S]+?\$\$|\\\[[\s\S]+?\\\]|\\\([\s\S]+?\\\)|\$[^$\n]+?\$|\*\*[^*]+\*\*|`[^`\n]+`)/g;let last=0;
 for(const match of text.matchAll(pattern)){container.append(document.createTextNode(text.slice(last,match.index)));const token=match[0],node=document.createElement(token.startsWith('**')?'strong':token.startsWith('`')?'code':'span');
 if(token.startsWith('**'))node.textContent=token.slice(2,-2);else if(token.startsWith('`'))node.textContent=token.slice(1,-1);else{const display=token.startsWith('$$')||token.startsWith('\\['),size=token.startsWith('\\')||token.startsWith('$$')?2:1;node.className=display?'chat-math-block':'chat-math';try{if(!window.katex)throw Error();window.katex.render(token.slice(size,-size),node,{displayMode:display,throwOnError:false,trust:false,strict:'ignore',maxExpand:200,maxSize:20});}catch{node.textContent=token;}}container.append(node);last=match.index+token.length;}container.append(document.createTextNode(text.slice(last)));
}
