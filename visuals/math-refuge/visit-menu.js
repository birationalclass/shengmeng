// The trigger and destination panel share one leave region, including its gap.
export function bindVisitMenu(dock,button,panel,{delay=3000,setTimer=setTimeout,clearTimer=clearTimeout}={}){
 let timer=null,open=false,pointerInside=false;
 const cancel=()=>{if(timer!==null)clearTimer(timer);timer=null;};
 const show=value=>{cancel();open=value;panel.hidden=!open;button.setAttribute('aria-expanded',String(open));dock.dataset.expanded=String(open);};
 const leave=()=>{cancel();if(open)timer=setTimer(()=>{timer=null;show(false);},delay);};
 button.addEventListener('click',()=>show(!open));
 dock.addEventListener('pointerenter',()=>{pointerInside=true;cancel();});
 dock.addEventListener('pointerleave',()=>{pointerInside=false;leave();});
 dock.addEventListener('focusin',cancel);
 dock.addEventListener('focusout',e=>{if(!dock.contains(e.relatedTarget)&&!pointerInside)leave();});
 dock.addEventListener('keydown',e=>{if(e.key==='Escape'){show(false);button.focus();}else if(e.key==='ArrowUp'&&e.target===button){e.preventDefault();show(true);panel.querySelector('button')?.focus();}});
 // Touch has no lasting hover: select a destination and put the menu away.
 panel.addEventListener('click',e=>{if(e.target.closest('button')&&matchMedia('(hover: none)').matches)show(false);});
 show(false);return {close:()=>show(false)};
}
