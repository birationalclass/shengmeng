// Labels and terms share the same unscaled coordinate plane. Align the actual
// rendered equality glyph, not the surrounding formula or its colon.
export function alignDiagramRelation(label){
 if(!label.classList.contains('relation-aligned')){label.style.removeProperty('--relation-offset');return;}
 const equals=[...label.querySelectorAll('.katex-html .mrel')].find(el=>el.textContent.includes('=')&&!el.closest('[data-math-old]'));
 if(!equals)return;
 const bounds=label.getBoundingClientRect(),width=parseFloat(label.style.width);
 if(!bounds.width||!width)return;
 // KaTeX may combine ':=' into one relation span. Measure only '='.
 const walker=document.createTreeWalker(equals,NodeFilter.SHOW_TEXT);let text;
 while((text=walker.nextNode())&&!text.textContent.includes('=')){}
 if(!text)return;
 const start=text.textContent.indexOf('='),range=document.createRange();
 range.setStart(text,start);range.setEnd(text,start+1);
 const glyph=range.getBoundingClientRect(),scale=bounds.width/width;
 const previous=parseFloat(label.style.getPropertyValue('--relation-offset'))||0;
 const offset=previous+(bounds.left+bounds.width/2-glyph.left-glyph.width/2)/scale;
 label.style.setProperty('--relation-offset',`${offset}px`);
}
