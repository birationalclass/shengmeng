export function fontStrokeControls(container,items,onSeek){
 container.replaceChildren();
 for(const item of items){
  const char=item.s.name.split(' · ')[0],plan=item.spec.mesh.strokePlan;
  for(const [i,phase] of plan.strokes.entries()){
   const row=document.createElement('div');row.className='stroke-row';
   const number=document.createElement('span');number.className='stroke-number';number.textContent=String(i+1);
   const button=document.createElement('button');button.type='button';button.textContent=char+' · '+phase.name;button.dataset.fontStroke=char+':'+i;
   button.onclick=()=>{for(const b of container.querySelectorAll('button'))b.removeAttribute('aria-current');button.setAttribute('aria-current','true');const at=phase.drawEnd+.8*(phase.end-phase.drawEnd);onSeek(item.s.start+(item.s.end-item.s.start)*at);};
   row.append(number,button);container.append(row);
  }
 }
}
