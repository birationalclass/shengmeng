export const GALAXIES=[
 {key:'C4',name:'ℤ/4ℤ',zh:'初光之境',en:'First light',order:4,color:0x70e3ff},
 {key:'S3',name:'S₃',zh:'交错双生',en:'Intertwined',order:6,color:0xe99cff},
 {key:'V4',name:'V₄',zh:'四象回声',en:'Four echoes',order:4,color:0x80ffe0},
 {key:'D4',name:'D₄',zh:'镜像星海',en:'Mirror sea',order:8,color:0xffbd79},
 {key:'Q8',name:'Q₈',zh:'深空八重奏',en:'Deep octet',order:8,color:0x9c9cff},
 {key:'S4',name:'S₄',zh:'万象旋臂',en:'Spiral worlds',order:24,color:0xff8dbf},
 {key:'S5',name:'S₅',zh:'群星交响',en:'Stellar symphony',order:120,color:0x9eeaff}
];
export function progress(value){return Math.max(0,Math.min(GALAXIES.length,Math.floor(Number(value)||0)));}
export function unlocked(index,completed){return index>=0&&index<GALAXIES.length&&index<=progress(completed);}
export function complete(index,completed){return unlocked(index,completed)?Math.max(progress(completed),index+1):progress(completed);}
