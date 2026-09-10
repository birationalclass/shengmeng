// A numbered page is a semantic unit, not an animation or a line of TeX.
// A map and its representative rule, or the two sides of an equality, stay together.
const groups={
 'learn:3':{section:2,first:1,items:[[1],[2]]},
 'learn:4':{section:2,first:3,items:[[1],[2,3]]},
 'learn:5':{section:2,first:5,items:[[1],[2],[3],[4]]},
 'converge:0':{section:3,first:1,items:[[1],[2],[3]]},
 'converge:1':{section:3,first:4,items:[[1],[2],[3]]},
 'converge:2':{section:3,first:7,items:[[1],[2,3]]},
 'converge:3':{section:3,first:9,items:[[1,2],[3,4],[5]]},
 'converge:4':{section:3,first:12,items:[[1],[2]]}
};
export function numberedPages(module,step,count){
 const group=groups[`${module}:${step}`]||{section:module==='lab'?4:5,first:1,items:Array.from({length:count},(_,i)=>[i+1])};
 return group.items.map((indices,i)=>({indices,number:`${group.section}.${group.first+i}`}));
}
// Retire the old text, resize the frame while empty, then reveal the new text.
// Only one numbered unit is visible at a time, including interrupted navigation.
export function createReadingPageMotion({duration}){
 const records=new WeakMap(),running=new Map();
 const show=(items,selected)=>items.forEach(el=>{el.hidden=!selected.includes(el);el.inert=el.hidden;});
 function settle(host){if(host)running.get(host)?.();else for(const finish of [...running.values()])finish();}
 function sync(host,items,selected){
  if(!host)return;
  const previous=records.get(host);if(previous&&previous.length===selected.length&&previous.every((el,i)=>el===selected[i]))return;
  settle(host);const old=items.filter(el=>!el.hidden),from=host.getBoundingClientRect().height;
  records.set(host,[...selected]);
  const ms=duration();if(!previous||!old.length||!selected.length||!ms||!host.getClientRects().length){show(items,selected);return;}
  const effects=[],style={height:host.style.height,overflow:host.style.overflow},end=()=>{
   effects.forEach(a=>a.cancel());show(items,selected);host.style.height=style.height;host.style.overflow=style.overflow;running.delete(host);host.removeAttribute('data-page-transition');
  };
  running.set(host,end);host.dataset.pageTransition='retiring';old.forEach(el=>{el.inert=true;});
  const animate=(el,frames,time)=>{const a=el.animate(frames,{duration:time,easing:'cubic-bezier(.33,0,.2,1)',fill:'both'});effects.push(a);return a;};
  const fades=old.map(el=>animate(el,[{opacity:getComputedStyle(el).opacity},{opacity:0}],ms*.2));
  Promise.all(fades.map(a=>a.finished)).then(()=>{
   if(running.get(host)!==end)return;
   show(items,selected);
   const holds=selected.map(el=>animate(el,[{opacity:0},{opacity:0}],1));
   const to=host.getBoundingClientRect().height;host.style.height=from+'px';host.style.overflow='hidden';host.dataset.pageTransition='frame';
   const frame=animate(host,[{height:from+'px'},{height:to+'px'}],ms*.5);
   frame.finished.then(()=>{
    if(running.get(host)!==end)return;
    host.style.height=style.height;host.style.overflow=style.overflow;frame.cancel();host.dataset.pageTransition='content';
    const enters=selected.map(el=>animate(el,[{opacity:0},{opacity:1}],ms*.3));holds.forEach(a=>a.cancel());
    Promise.all(enters.map(a=>a.finished)).then(()=>{if(running.get(host)===end)end();},()=>{});
   },()=>{});
  },()=>{});
 }
 window.addEventListener('resize',()=>settle());
 matchMedia('(prefers-reduced-motion:reduce)').addEventListener('change',e=>{if(e.matches)settle();});
 new MutationObserver(()=>{if(!duration())settle();}).observe(document.documentElement,{attributes:true,attributeFilter:['data-notebook-motion']});
 return {sync,settle};
}
