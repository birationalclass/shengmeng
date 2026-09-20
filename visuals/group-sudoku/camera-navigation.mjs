// Frame-rate-independent camera dolly; Up approaches the target, Down recedes.
export function dollyRadius(radius,direction,dt){return Math.max(16,Math.min(230,radius*Math.exp(-direction*Math.min(.08,Math.max(0,dt))*.72)));}
export function panDistance(radius,direction,dt){return radius*direction*Math.min(.08,Math.max(0,dt))*.30;}
export function cameraKey(event){return !event.shiftKey&&!event.altKey&&!event.ctrlKey&&!event.metaKey&&['ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(event.key);}
