import {BUILDING_SCALE as S} from './site-layout.js?v44-hall-clearance';
// Metres in world space. East edge -1135 is >1 km west of campus deck -95*S.
export const RESIDENCE={origin:[-1190,0,0],halfWidth:55,halfDepth:43,floor:.9,roof:5.2};
export const residenceGap=()=>Math.abs(RESIDENCE.origin[0])-RESIDENCE.halfWidth-95*S;
const view=(name,position,target,description)=>({name,title:name,description,duration:28,fov:58,residence:true,positions:[position,position].map(p=>[(p[0]+RESIDENCE.origin[0])/S,p[1]/S,p[2]/S]),targets:[target,target].map(p=>[(p[0]+RESIDENCE.origin[0])/S,p[1]/S,p[2]/S])});
export const RESIDENCE_SHOTS=[
 view('海上住宅',[44,21,46],[0,2,0],'独立住宅岛 · 距园区边缘约 1 公里 · 石、木与海风'),
 view('住宅玄关',[9,2.55,12],[1,2.4,-10],'学术足迹 · 从新加坡到上海'),
 view('住宅书房',[-12,2.5,-2],[-12,2.15,-11.9],'研究书架 · 论文与预印本 · 海景书桌'),
 view('住宅展廊',[1.5,2.5,-4.3],[1.5,2.3,-12],'可视化收藏 · 数学结构的空间表达'),
 view('住宅工作室',[13,2.5,-3.5],[13,2.05,-11.7],'AI4Math · msreader · AI4Games'),
 view('住宅客厅',[10,2.5,10],[-1,1.8,1.8],'会客与交流 · 暖木、织物与庭院'),
 view('住宅套房',[-9,2.5,11],[-15,1.6,5],'安静的生活空间 · 衣帽与独立浴室'),
 view('住宅露台',[12,2.5,21],[32,1,7],'海景茶席 · 浅水庭院 · 日出')
];
export const RESIDENCE_ROOMS=[['玄关 · 学术足迹','住宅玄关'],['书房 · 论文收藏','住宅书房'],['展廊 · 数学可视化','住宅展廊'],['工作室 · AI 与游戏','住宅工作室'],['会客厅 · 交流','住宅客厅'],['主卧套房','住宅套房'],['海景露台','住宅露台']].map(([name,shot])=>({name,shot}));
