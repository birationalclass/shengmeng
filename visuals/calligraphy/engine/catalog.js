import {glyphs} from './glyphs.js';
import {qi} from './signature-glyphs.js';
import {phraseGlyphs} from './phrase-glyphs.js';
import {brushGlyphs,windStudy} from './brush-glyphs.js';

// Local interpretations, not the author's recovered meshes or parameters.
const sources={
 '01':{name:'趙孟頫《閒居賦》',phrase:'長楊映沼',url:'https://digitalarchive.npm.gov.tw/Collection/Detail?dep=P&id=314',image:'assets/references/01-原帖局部.png',caption:'故宫原帖局部 · 原始像素 · CC BY 4.0',description:'长横轻挑，内撇收锋，外钩回抱。'},
 '02':{name:'文徵明 · 扇面行书',phrase:'右追和楊鐵崖石湖花游曲',url:'https://digitalarchive.npm.gov.tw/opendata/Pub/DetailEng/15389?dep=P&mode=full',image:'assets/references/02-原帖局部.png',caption:'故宫原帖局部 · 原始像素 · CC BY 4.0',description:'扇面字势转正。细腰、牵丝与提锋形成较轻的节奏。'},
 '03':{name:'趙孟頫《急就章》',phrase:'柏杜楊',url:'https://digitalarchive.npm.gov.tw/opendata/Pub/DetailEng/746?dep=P&mode=full',image:'assets/references/03-原帖局部.png',caption:'故宫原帖局部 · 原始像素 · CC BY 4.0',description:'章草取势更开张，保留侧锋的厚薄对比和草化回转。'}
};
const medians=[
 [[326,698],[350,691],[403,691],[654,741],[700,747],[727,744]],
 [[179,421],[204,414],[238,414],[519,462],[749,490],[800,484],[839,472]],
 [[438,664],[485,643],[491,633],[466,401],[450,336],[424,268],[394,216],[340,158],[212,87],[134,63]],
 [[505,431],[510,408],[533,366],[596,270],[714,122],[771,78],[947,35]]
];
const widths=[
 [.015,.08,.13,.11,.12,.075,.008],
 [.006,.085,.12,.135,.16,.10,.005],
 [.035,.15,.115,.12,.145,.11,.002],
 [.012,.075,.13,.19,.21,.13,.002]
];
const names=['上横 · 逆入提收','下横 · 按行转锋','长撇 · 转折出锋','长捺 · 舒展收尖'];
const starts=[.06,.42,.98,1.72],ends=[.36,.91,1.65,2.42];
const depths=[u=>.20*Math.sin(u*Math.PI*1.2),u=>-.16+.20*Math.sin(u*Math.PI),u=>.11+.23*Math.sin(u*5.2),u=>.14-.29*Math.sin(u*3.8)];
const rolls=[[-.5,.7,-.25,.5],[.35,-.55,.4,-.4],[-.3,.38,-.38,.7],[.6,-.45,.4,-.3]];
const sky={id:'tian',text:'天',title:'舒展',subtitle:'两横蓄势，撇捺舒展',kind:'centerline',duration:6,writeStart:.06,writeEnd:2.42,frontalAt:4.35,
 strokes:medians.map((points,i)=>({name:names[i],points:points.map(([x,y],j)=>[(x-520)*.0037,(y-420)*.0037,depths[i](j/(points.length-1))]),width:widths[i],thickness:widths[i].map(w=>.018+w*.55),roll:rolls[i],entry:.025,exit:.045,start:starts[i],end:ends[i],motion:[0,.08,.34,.69,.88,1]})),
 source:{name:'天 · 本地曲面重建',phrase:'沿用已有四笔中线，重新构建截面与空间层次',url:'https://github.com/chanind/hanzi-writer-data',image:'assets/legacy-tian.jpg',caption:'本地旧版模型预览 · 非原帖',description:'中线来自已有 Hanzi Writer Data 数据；体量、扭转和深度为本项目设计。保留原有 ARPHICPL 许可。'}
};
export const catalog=[
 ...glyphs.map(g=>({...g,kind:'rail',source:sources[g.id]})),
 {...windStudy,id:'feng',kind:'rail',title:'回环',subtitle:'宽面回卷，连势铺锋',source:{name:'風 · 原片轮廓与运笔校准',phrase:'薄煙 @boyanidea · BV1PP4y1Z7Zv 的 2022-07-27 作品',url:'https://www.bilibili.com/video/BV1PP4y1Z7Zv/',image:'assets/wind-preview.png',caption:'本地空间笔势研究 · 非作者原模型',description:'根据原片约 7.47、7.68、8.19、8.75 秒画面校准。v11针对第二笔横折弯钩到第三笔：长外缘绕过右下钩面，沿内缘向上回卷，移锋后承接第三笔；保留原片成字的两笔间空隙。可选运笔轨迹仅为辅助线，不属于成字模型。v10内撇接虫的版本单独保留，不能代替这次二→三的动作。保留虫左侧越过第一笔的深度关系，以及v9分段接笔、v8造型对比。深度、材质与运镜均为本地拟合；未取得作者原模型或关键帧，可在笔势面板同角度切回v8比较。'}},
 sky,qi,...phraseGlyphs,...brushGlyphs
];

// Gold / silver / green observed in BV16a4y1P7fA. Other colors are extensions.
export const materialPresets={
 gold:{name:'流金',color:'#b79d63',metalness:.96,roughness:.22,clearcoat:.18,anisotropy:.12,ridges:0},
 silver:{name:'镜面银',color:'#c2c7ca',metalness:1,roughness:.12,clearcoat:.12,anisotropy:0,ridges:0},
 green:{name:'青绿',color:'#536839',metalness:.65,roughness:.23,clearcoat:.72,anisotropy:.28,ridges:0},
 cobalt:{name:'钴蓝',color:'#234d78',metalness:.72,roughness:.22,clearcoat:.62,anisotropy:.35,ridges:0},
 rose:{name:'玫瑰金',color:'#b77861',metalness:.91,roughness:.26,clearcoat:.35,anisotropy:.42,ridges:0},
 ink:{name:'墨玉',color:'#172227',metalness:.36,roughness:.22,clearcoat:.85,anisotropy:.15,ridges:0},
 porcelain:{name:'素瓷',color:'#e9e2d4',metalness:.02,roughness:.31,clearcoat:.52,anisotropy:0,ridges:0},
 bronze:{name:'古铜',color:'#806044',metalness:.87,roughness:.36,clearcoat:.15,anisotropy:.36,ridges:0}
};

// Kept verbatim from 备份/2026-10-24-广逐笔塑形前/catalog.js.
// Material versions are independent of the selected calligraphy model.
export const classicMaterialPresets={
 gold:{name:'流金',color:'#c19a46',metalness:.94,roughness:.25,clearcoat:.38,anisotropy:.42,ridges:.46},
 silver:{name:'拉丝银',color:'#aeb6ba',metalness:.94,roughness:.27,clearcoat:.24,anisotropy:.65,ridges:.64},
 green:{name:'青绿',color:'#536839',metalness:.65,roughness:.23,clearcoat:.72,anisotropy:.28,ridges:.55},
 cobalt:{name:'钴蓝',color:'#234d78',metalness:.72,roughness:.22,clearcoat:.62,anisotropy:.35,ridges:.45},
 rose:{name:'玫瑰金',color:'#b77861',metalness:.91,roughness:.26,clearcoat:.35,anisotropy:.42,ridges:.42},
 ink:{name:'墨玉',color:'#172227',metalness:.36,roughness:.22,clearcoat:.85,anisotropy:.15,ridges:.27},
 porcelain:{name:'素瓷',color:'#e9e2d4',metalness:.02,roughness:.31,clearcoat:.52,anisotropy:0,ridges:.18},
 bronze:{name:'古铜',color:'#806044',metalness:.87,roughness:.36,clearcoat:.15,anisotropy:.36,ridges:.54}
};
export const materialVersions={
 smooth:{name:'新版光滑',description:'光滑笔面与圆边，预设关闭纵向起伏。',presets:materialPresets},
 classic:{name:'旧版拉丝',description:'恢复此前八种材质的原参数，保留纵向笔触与拉丝反光。',presets:classicMaterialPresets}
};
