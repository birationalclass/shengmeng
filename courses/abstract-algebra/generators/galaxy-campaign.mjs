export const GALAXIES=[
 {key:'C4',name:'C₄',zh:'初光之境',en:'First light',order:4,color:0x70e3ff},
 {key:'V4',name:'V₄',zh:'两仪生四象',en:'Four images from two forces',order:4,color:0x80ffe0},
 {key:'S3',name:'S₃',zh:'交错双生',en:'Intertwined',order:6,color:0xe99cff},
 {key:'D4',name:'D₄',zh:'镜像星海',en:'Mirror sea',order:8,color:0xffbd79},
 {key:'Q8',name:'Q₈',zh:'深空八重奏',en:'Deep octet',order:8,color:0x9c9cff},
 {key:'S4',name:'S₄',zh:'可解之巅',en:'Summit of solvability',order:24,color:0xff8dbf},
 {key:'F56',name:'AGL(1,𝔽₈)',zh:'华夏星群',en:'Huaxia constellation',order:56,color:0xffb87d},
 {key:'A5',name:'A₅',zh:'不可约之夜',en:'The indivisible night',order:60,color:0xbca8ff},
 {key:'S5',name:'S₅',zh:'伽罗华之心',en:'Heart of Galois',order:120,color:0x9eeaff}
];
export function progress(value){return Math.max(0,Math.min(GALAXIES.length,Math.floor(Number(value)||0)));}
export function unlocked(index,completed){return index>=0&&index<GALAXIES.length&&index<=progress(completed);}
export function complete(index,completed){return unlocked(index,completed)?Math.max(progress(completed),index+1):progress(completed);}
