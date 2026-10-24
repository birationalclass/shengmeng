import {wind as original} from './wind-data.js';

// Local reconstruction from the creator's 2022-07-27 風, visible at 8.745 s.
// These are traced image-space controls and authored depths, NOT recovered
// artist controls. Floating Strokes §4.1 / the author's BV1tm4y1a7uH explain
// the two boundary + two volume-curve construction used here.
const imagePoint=([x,y,z])=>[(x-574)/120,(355-y)/120,z];
const inner=[
 [503,228,-.10],[504,247,-.13],[522,267,-.10],[545,280,.02],
 [561,257,.09],[573,240,.07],[577,234,.03],[579,231,0],
 [580,231,-.01],[581,232,-.02],[582,234,-.03],[583,237,-.04],
 [584,241,-.05],[585,245,-.05],[586,249,-.07],[589,307,-.09],
 [595,364,-.08],[603,410,-.06],[613,461,-.07],[646,514,.10],
 [688,552,.24],[732,578,.32],[762,577,.27],[757,531,-.22]
];
const outer=[
 [503,228,-.10],[521,222,-.05],[540,210,-.02],[560,199,-.05],
 [578,178,-.10],[586,159,-.14],[596,143,-.14],[609,136,-.07],
 [624,139,.04],[638,150,.18],[643,164,.30],[639,180,.35],
 [626,197,.15],[619,224,.03],[617,249,.02],[613,307,.01],
 [615,364,0],[624,409,-.01],[674,446,-.14],[720,479,-.22],
 [766,501,-.20],[786,529,-.02],[782,544,.12],[757,531,-.22]
];

// Times are fitted to the approximately two-second writing section. Separate
// strokes carry the gesture without an invented permanent bridge across air.
const times=[[.04,.25],[.27,1.08],[1.08,1.50],[1.51,1.59],
 [1.60,1.78],[1.79,1.88],[1.89,2.06],[2.07,2.20],[2.21,2.31]];
const mainTiming=[[0,0],[.10,.08],[.24,.25],[.37,.36],[.52,.52],
 [.66,.71],[.80,.88],[.92,.97],[1,1]];
const mainGesture={timing:mainTiming,anchor:'a',wake:.095,pressure:[.55,.85,1,.60,.40,.60,.90,.45],roll:[-.10,.12,.08,-.12,.06,.20,-.18,0],
 phases:[[0,'逆入蓄势'],[.15,'转锋折肩'],[.36,'提锋下行'],[.63,'按笔铺面'],[.88,'回卷上挑']]};

const strokes=original.strokes.map((s,i)=>({
 ...s,a:s.a.map(([x,y,z])=>[x*1.10+.04,y*1.10,z]),
 b:s.b.map(([x,y,z])=>[x*1.10+.04,y*1.10,z]),
 start:times[i][0],end:times[i][1],brush:'reference-four-rail-v1',
 boundaryLoft:true,safeBend:false,capStart:0,capEnd:0,
 crown:[.5,.54,.5],rearCrown:[.5,.48,.5],camber:[0,0],
 gesture:i===1?mainGesture:{anchor:'a',wake:.065,pressure:[.6,1,.85,.4],roll:[-.08,.10,0],
  timing:[[0,0],[.13,.06],[.40,.32],[.72,.78],[1,1]],phases:[[0,'承势入笔'],[.15,'按行'],[.84,'转锋提收']]},
 ...(i===1?{role:'wind-main'}:i===2?{role:'wind-inner',connection:{from:'wind-main',type:'gesture'},name:'内撇 · 承二笔势'}:{})
}));
Object.assign(strokes[1],{
 a:inner.map(imagePoint),b:outer.map(imagePoint),interpolateBoundaries:true,
 front:[.25,.30,.28,.24,.19,.12,.075,.065,.065,.075,.10,.14,.22,.25],
 back:[.16,.20,.18,.15,.11,.075,.045,.035,.035,.045,.065,.085,.14,.18],
 camber:[0,.02,.01,0,0,0,0,0,0,0,-.035,-.065,-.075,0],
 crown:[.48,.52,.53,.50,.49],rearCrown:[.50,.48,.50]
});
// The inner 撇 has a short returning inner edge and a much longer outer
// shoulder. Sending BOTH edges around the shoulder makes a hollow loop.
Object.assign(strokes[2],{
 // The shoulder uses smoothed fitted controls. Interpolating every manually
 // estimated point here produces a near-tangent correspondence and a ripple.
 interpolateBoundaries:false,
 a:[[467,300,.04],[468,322,.05],[479,343,.07],[491,351,.10],
  [500,343,.15],[504,336,.18],[508,333,.20],[512,333,.23],
  [506,350,.26],[492,377,.28],[470,412,.25],[455,448,.15],
  [454,464,.06],[458,475,.02],[473,478,0]].map(imagePoint),
 b:[[467,300,.04],[482,311,.04],[498,315,.03],[514,309,.02],
  [533,291,.08],[549,286,.18],[567,291,.30],[576,303,.38],
  [574,320,.40],[558,346,.36],[536,377,.32],[513,417,.26],
  [495,449,.17],[482,472,.08],[473,478,0]].map(imagePoint),
 front:[.26,.38,.46,.43,.32,.18],back:[.16,.24,.28,.26,.19,.10],
 crown:[.48,.57,.53],camber:[0,.025,-.025,0],
 gesture:{anchor:'a',wake:.09,pressure:[.5,.9,1,.7,.35],roll:[-.08,.14,-.06,0],
  timing:[[0,0],[.20,.025],[.45,.12],[.62,.40],[.85,.80],[1,1]],
  phases:[[0,'承势落锋'],[.07,'按笔成肩'],[.28,'转锋长撇'],[.86,'提收入内']]}
});
strokes[0].front=strokes[0].front.map(v=>v*.70);
strokes[0].back=strokes[0].back.map(v=>v*.78);
strokes[0].camber=[0,.015,-.06,-.09,0];
Object.assign(strokes[6],{
 interpolateBoundaries:true,
 a:[[500,371,.29],[506,398,.32],[507,439,.29],[501,479,.16],[489,512,.02],[482,540,-.09]].map(imagePoint),
 b:[[500,371,.29],[526,407,.43],[532,446,.44],[523,488,.31],[507,523,.10],[482,540,-.09]].map(imagePoint),
 front:[.28,.40,.44,.34,.16],back:[.17,.25,.28,.20,.10],camber:[0,.02,-.02,0]
});

export const windReference={...original,strokes,legacyStrokes:original.strokes,
 duration:6,writeStart:.04,writeEnd:2.31,frontalAt:3.65,
 revision:'wind-reference-boundary-v8-20261024',
 calibration:{referenceTime:8.745172,coordinates:'x=(px-574)/120, y=(355-py)/120',
  source:'https://www.bilibili.com/video/BV1PP4y1Z7Zv/',
  scope:'Manually traced main-stroke image contours; authored depth and timing. No original mesh, material file, or animation keys were obtained.'},
 method:'Paired boundary-preserving cubic surfaces and two separately shaped volume rails. Single-edge-anchored growth. Temporal stroke-2-to-3 gesture; no invented hairline bridge.'
};

export const windReferencePreset={preset:'silver',materialPreset:'silver',materialVersion:'smooth',
 color:'#bfc2c4',metalness:1,roughness:.26,clearcoat:.14,anisotropy:0,ridges:0,
 fullness:1,depth:1,turn:1,layering:.30,harmony:.50,
 model:'spatial',writing:'flow',connection:'linked',lighting:'reference',background:'stone',display:'plain',
 azimuth:-28,keyPower:2.4,environment:.85,exposure:.95,shadows:true,wireframe:false,guides:false,explode:0};
