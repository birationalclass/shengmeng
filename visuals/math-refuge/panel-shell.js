// Each header stays outside the content scrollport. Keep its original DOM identity.
export function preparePanelShell(panel){
 if(!panel||panel.querySelector(':scope > .panel-content'))return;
 const heading=panel.firstElementChild;if(!heading)return;
 const content=panel.ownerDocument.createElement('div');content.className='panel-content';
 while(heading.nextSibling)content.append(heading.nextSibling);
 panel.append(content);panel.classList.add('panel-shell');
}
export function bindPanelDismissals(doc,panels){
 function outside(event){
  if(event.button!==undefined&&event.button!==0)return;
  const path=event.composedPath?.()||[];
  for(const {panel,triggers=[],close} of panels){
   if(!panel||panel.hidden||path.includes(panel)||panel.contains(event.target)||triggers.some(t=>t&&(path.includes(t)||t.contains(event.target))))continue;
   close();
  }
 }
 doc.addEventListener('click',outside,true);
 return()=>doc.removeEventListener('click',outside,{capture:true});
}
