import {BUILDING_SCALE as S,DECK_Y} from './site-layout.js?v44-hall-clearance';
const upperEye=2*DECK_Y+3.2/S+.20+1.5/S;
export const BUILDINGS=[
  {number:1,name:'报告厅',shot:'报告厅',roof:'Upper seminar lounge',rooms:[{name:'一层 · 报告厅',shot:'报告厅',room:0},{name:'二层 · 客厅',shot:'二楼客厅'}]},
  {number:2,name:'教学楼',shot:'教学楼',rooms:[{name:'一层 · KM 研读教室',room:1},{name:'二层 · 教室',room:2},{name:'三层 · 教室',room:3}]},
  {number:3,name:'图书馆',shot:'书室',roof:'Independent quiet library',rooms:[{name:'阅览室',shot:'书室'}]},
  {number:4,name:'学术客厅',shot:'学术客厅',roof:'Upper private studies',rooms:[{name:'一层 · 客厅',shot:'学术客厅'},{name:'二层 · 书房',shot:'楼上书房'}]},
  {number:5,name:'讨论楼',shot:'讨论楼',roof:'Upper small seminar',rooms:[{name:'一层 · 讨论室',shot:'讨论楼'},{name:'二层 · 小讨论室',shot:'楼上讨论室'}]},
  {number:6,name:'咖啡屋',shot:'咖啡屋',roof:'North coffee cabin',rooms:[{name:'咖啡室',shot:'咖啡屋'}]},
  {number:7,name:'茶室',shot:'茶室',roof:'Service and tea kitchen',rooms:[{name:'茶室与厨房',shot:'茶室'}]},
  {number:8,name:'客舍一',shot:'客舍一',roof:'Quiet residential villa 1',rooms:[{name:'客房',shot:'客舍一'}]},
  {number:9,name:'客舍二',shot:'客舍二',roof:'Quiet residential villa 2',rooms:[{name:'客房',shot:'客舍二'}]}
];
export const OUTDOOR_AREAS=['庭院','海景露台','海上花园'];
export const buildingForShot=name=>BUILDINGS.find(b=>b.shot===name||b.rooms.some(r=>r.shot===name));
const viewpoint=(name,position,target)=>({name,title:name,description:'自由观察 · 拖动改变视角',duration:25,fov:58,positions:[position,[...position]],targets:[target,[...target]]});
// Interior viewpoints are in the same plan coordinates as the original tour.
export const BUILDING_SHOTS=[
  viewpoint('学术客厅',[-6,DECK_Y+1.6/S,2],[-6,1.2,-5]),
  viewpoint('楼上书房',[-7,upperEye,-3],[-7,upperEye-.3,-8]),
  viewpoint('讨论楼',[11.5,DECK_Y+1.6/S,2],[11.5,1.2,-5]),
  viewpoint('楼上讨论室',[11,upperEye,-3],[11,upperEye-.3,-8]),
  viewpoint('咖啡屋',[39,DECK_Y+1.6/S,-19.8],[39,1.2,-23]),
  viewpoint('茶室',[-32.5,DECK_Y+1.6/S,20],[-38,1.2,19]),
  viewpoint('客舍一',[-53.5,DECK_Y+1.6/S,-27],[-57,1.2,-28]),
  viewpoint('客舍二',[-44.5,DECK_Y+1.6/S,-37],[-48,1.2,-38])
];
