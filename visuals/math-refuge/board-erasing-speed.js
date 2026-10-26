// Ratios use the existing 2026-10-26 eraser motion as the 1x baseline.
export const DEFAULT_ERASING_SPEED=2,MIN_ERASING_SPEED=.5,MAX_ERASING_SPEED=4;
export const ERASING_SPEED_KEY='refuge-board-erasing-speed-v1';
export function normalizeErasingSpeed(value){
 const n=Number(value);
 if(value==null||value===''||!Number.isFinite(n)||n<=0)return DEFAULT_ERASING_SPEED;
 return Math.max(MIN_ERASING_SPEED,Math.min(MAX_ERASING_SPEED,Math.round(n*4)/4));
}
export function loadErasingSpeed(storage){try{storage=storage===undefined?globalThis.localStorage:storage;return normalizeErasingSpeed(storage?.getItem(ERASING_SPEED_KEY));}catch{return DEFAULT_ERASING_SPEED;}}
export function saveErasingSpeed(value,storage){const rate=normalizeErasingSpeed(value);try{storage=storage===undefined?globalThis.localStorage:storage;storage?.setItem(ERASING_SPEED_KEY,String(rate));}catch{}return rate;}
// Only discard measured pre-writing silence after contact AND the return finish.
// Never shorten a narrated interval, reading hold, question or manual pause.
export function eraseSilenceTarget(manifest,board,time,run,eraserState){
 if(!board||board.page<6||!run||run.page!==board.page||run.elapsed<run.duration||eraserState!=='resting')return null;
 const target=board.writeStart;
 if(!Number.isFinite(time)||!Number.isFinite(target)||time<board.eraseStart||time>=target-.025)return null;
 if(!Array.isArray(manifest?.paragraphs)||!manifest.paragraphs.length||!board.lineCues?.length)return null;
 const speech=manifest.paragraphs.filter(p=>p.page===board.page);
 if(!speech.length||speech.some(p=>!Number.isFinite(p.start)||!Number.isFinite(p.end)||p.start<target&&p.end>time))return null;
 return target;
}
