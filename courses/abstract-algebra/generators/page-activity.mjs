// Window focus and page visibility are independent (including split-window use).
export function watchPageActivity(onChange,host=window){
 let focused=host.document.hasFocus();
 const active=()=>focused&&!host.document.hidden;
 const emit=()=>onChange(active());
 const blur=()=>{focused=false;emit();};
 const focus=()=>{focused=true;emit();};
 const visibility=()=>{focused=host.document.hasFocus();emit();};
 host.addEventListener('blur',blur);host.addEventListener('focus',focus);
 host.document.addEventListener('visibilitychange',visibility);emit();
 return ()=>{host.removeEventListener('blur',blur);host.removeEventListener('focus',focus);host.document.removeEventListener('visibilitychange',visibility);};
}
