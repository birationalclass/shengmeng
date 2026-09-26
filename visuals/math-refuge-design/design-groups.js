let active='',serial=0;
export const decorationGroup=()=>active;
export function decoration(name,fn){return function(...args){const old=active;active=old||name+'-'+(++serial);try{return fn(...args);}finally{active=old;}};}
