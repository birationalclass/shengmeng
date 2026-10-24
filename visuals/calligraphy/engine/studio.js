import {icons} from '../icons.js';
import {convertScript} from '../script-conversion.js';
import * as T from '../vendor/three.module.js';
import {RoomEnvironment} from '../vendor/RoomEnvironment.js';
import {OrbitControls} from '../vendor/OrbitControls.js';
import {profile} from './stroke-volume.js';
import {catalog,materialPresets,classicMaterialPresets,materialVersions} from './catalog.js';
import {createVolume,updateVolume} from './surface.js?v=16';
import {zipStore,modelFiles} from './export-format.js';
import {createTextGlyph,cleanText} from './text-engine.js?v=16';
import {prepareSpatialModel,constructionCurves} from './spatial-model.js?v=16';
import {sampleRailSection} from './yang-volume.js';
import {writingProgress,writingPhase} from './brush-gesture.js?v=16';
import {windReferencePreset,windReferencePresetV8} from './wind-reference.js';
import {createReferenceEnvironment} from './reference-environment.js';

const $=id=>document.getElementById(id),canvas=$('canvas');
const defaults={preset:'ink',materialPreset:'ink',materialVersion:'classic',...classicMaterialPresets.ink,writingScript:'traditional',glyphStyle:'cursive',writing:'flow',connection:'linked',model:'spatial',turn:1,layering:1,harmony:.5,guides:false,trajectory:false,fullness:1,depth:1,explode:0,lighting:'reference-v9',background:'stone',display:'plain',azimuth:-35,keyPower:2.8,environment:1,exposure:1,shadows:true,wireframe:false};
let renderScale=1.25;
const emptyGlyph={id:'empty',text:'',title:'',subtitle:'',strokes:[],duration:0,writeStart:0,writeEnd:0,frontalAt:0,charSources:[],source:{name:'',phrase:'',url:'',image:'',caption:'',description:''}};
let settings={...defaults},glyph=emptyGlyph,items=[],time=0,paused=true,speed=1,follow=true,spinning=false,dirty=true,shapeDirty=false,lastYang='01',viewRadius=8.4,buildRevision=0,building=false,recording=null,seamPlayback=null;
const renderer=new T.WebGLRenderer({canvas,antialias:true,preserveDrawingBuffer:true,powerPreference:'high-performance'});
renderer.setPixelRatio(1);renderer.outputColorSpace=T.SRGBColorSpace;renderer.toneMapping=T.ACESFilmicToneMapping;renderer.shadowMap.enabled=true;renderer.shadowMap.type=T.PCFShadowMap;
const scene=new T.Scene(),camera=new T.PerspectiveCamera(30,1,.1,200),target=new T.Vector3(0,1.9,0),modelBounds=new T.Box3();
camera.position.set(0,target.y,8.4);camera.lookAt(target);
const controls=new OrbitControls(camera,canvas);controls.target.copy(target);controls.enableDamping=true;controls.dampingFactor=.1;controls.rotateSpeed=.65;controls.minDistance=4.8;controls.maxDistance=24;controls.maxPolarAngle=Math.PI*.68;controls.update();
const pmrem=new T.PMREMGenerator(renderer),room=new RoomEnvironment(),environmentTarget=pmrem.fromScene(room,.065);scene.environment=environmentTarget.texture;room.dispose();pmrem.dispose();
const referenceEnvironment=createReferenceEnvironment(renderer);
const referenceEnvironmentV9=createReferenceEnvironment(renderer,'v9');
const floor=new T.Mesh(new T.PlaneGeometry(160,160),new T.ShadowMaterial({color:0x555555,opacity:.13}));floor.rotation.x=-Math.PI/2;floor.receiveShadow=true;scene.add(floor);
const hemisphere=new T.HemisphereLight(0xffffff,0x666666,.6);scene.add(hemisphere);
const key=new T.DirectionalLight(0xfffcf3,2.8);key.castShadow=true;key.shadow.mapSize.set(2048,2048);Object.assign(key.shadow.camera,{left:-4.5,right:4.5,top:5,bottom:-4,near:.1,far:100});key.shadow.normalBias=.008;key.shadow.bias=-.00008;key.shadow.radius=4;scene.add(key);scene.add(key.target);
const rim=new T.DirectionalLight(0xe1eaf7,1.4);rim.position.set(4,5,-4);scene.add(rim);
const mat=new T.MeshPhysicalMaterial({color:settings.color,metalness:settings.metalness,roughness:settings.roughness,clearcoat:settings.clearcoat,clearcoatRoughness:.22,anisotropy:settings.anisotropy,envMapIntensity:1});
const group=new T.Group();group.position.copy(target);scene.add(group);
const guides=new T.Group();group.add(guides);let modelReport={},penTransfers=[];
const transferGuides=new T.Group();group.add(transferGuides);
const transferMaterial=new T.LineDashedMaterial({color:0xb77340,transparent:true,opacity:.72,dashSize:.045,gapSize:.03,depthTest:false});
const penFront=new T.Mesh(new T.SphereGeometry(.027,12,8),new T.MeshBasicMaterial({color:0xb86d35,depthTest:false}));penFront.renderOrder=8;transferGuides.add(penFront);
function rebuildTransferGuide(){
 for(const line of [...transferGuides.children])if(line!==penFront){transferGuides.remove(line);line.geometry.dispose();}
 if(!penTransfers.length)return;const main=items.find(p=>p.s.role==='wind-main'),inner=items.find(p=>p.s.role==='wind-inner');if(!main||!inner)return;
 const points=[];for(let i=0;i<=80;i++)points.push(sampleRailSection(main.spec,.48+.52*i/80).b);
 for(const p of penTransfers[0].curve.getPoints(40).slice(1))points.push(p);
 for(let i=1;i<=20;i++)points.push(sampleRailSection(inner.spec,i/100).a);
 const line=new T.Line(new T.BufferGeometry().setFromPoints(points),transferMaterial);line.computeLineDistances();line.renderOrder=7;transferGuides.add(line);
}
function updateTransferGuide(){
 transferGuides.visible=settings.trajectory&&penTransfers.length>0&&settings.connection==='linked'&&settings.writing==='flow';if(!transferGuides.visible)return;
 const air=penTransfers.find(p=>time>=p.start&&time<p.end),main=items.find(p=>p.s.role==='wind-main'),inner=items.find(p=>p.s.role==='wind-inner');if(!main||!inner)return;
 penFront.visible=time>=main.s.start&&time<=inner.s.end;if(air){penFront.position.copy(air.curve.getPoint((time-air.start)/(air.end-air.start)));return;}
 const item=time<inner.s.start?main:inner,u=T.MathUtils.clamp((time-item.s.start)/(item.s.end-item.s.start),0,1),q=sampleRailSection(item.spec,writingProgress(item.spec,u,settings.writing));penFront.position.copy(item===main?q.b:q.a);
}
const guideMaterials=[0x688b8f,0x688b8f,0x297b64,0xb67643,0x8e788e].map(color=>new T.LineBasicMaterial({color,transparent:true,opacity:.85,depthTest:false}));
const displayGroup=new T.Group();scene.add(displayGroup);
const boardMaterial=new T.MeshStandardMaterial({color:0xecece5,roughness:.72});
const circle=new T.Mesh(new T.CylinderGeometry(2.30,2.30,.10,96),boardMaterial);circle.rotation.x=Math.PI/2;
const square=new T.Mesh(new T.BoxGeometry(4.65,4.65,.10),boardMaterial),plinth=new T.Mesh(new T.BoxGeometry(4.8,.13,2.8),boardMaterial);
for(const mesh of [circle,square,plinth]){mesh.receiveShadow=true;mesh.castShadow=true;displayGroup.add(mesh);}
const numeric={metalness:[0,1],roughness:[.08,.85],clearcoat:[0,1],anisotropy:[0,1],ridges:[0,1],fullness:[.5,1.5],depth:[0,2],turn:[0,1.5],layering:[0,1.5],harmony:[0,1],explode:[0,1],azimuth:[-150,150],keyPower:[0,6],environment:[.1,2.5],exposure:[.5,1.7]};
const enums={writingScript:['traditional','simplified','original'],glyphStyle:['cursive','original'],lighting:['soft','rim','warm','reference','reference-v9'],background:['stone','dark','paper'],display:['plain','circle','square'],model:['spatial','reference-v10','reference-v9','reference-v8','legacy'],materialVersion:['smooth','classic'],writing:['flow','reveal'],connection:['linked','separate']};
const duration=()=>glyph?.duration||0;
let noticeTimeout;function notice(text){$('notice').textContent=text;$('notice').hidden=false;clearTimeout(noticeTimeout);noticeTimeout=setTimeout(()=>$('notice').hidden=true,4400);}
function feedback(text,error=false){if(error)notice(text);$('text-feedback').textContent=text;$('text-feedback').classList.toggle('error',error);$('text-form').classList.toggle('invalid',error);$('text-input').setAttribute('aria-invalid',String(error));}
function updateOutputs(){for(const id of Object.keys(numeric)){const out=document.querySelector(`output[for="${id}"]`);if(out)out.textContent=id==='azimuth'?Math.round(settings[id])+'°':settings[id].toFixed(2);}}
function syncUI(){for(const id of [...Object.keys(numeric),...Object.keys(enums),'color'])$(id).value=settings[id];for(const id of ['shadows','wireframe','guides','trajectory'])$(id).checked=settings[id];const version=materialVersions[settings.materialVersion];$('material-version-note').textContent=version.description;document.querySelectorAll('[data-preset]').forEach(b=>{const preset=version.presets[b.dataset.preset];b.setAttribute('aria-pressed',String(b.dataset.preset===settings.preset));b.title=preset.name;b.style.setProperty('--swatch',preset.color);b.querySelector('span').textContent=preset.name;});document.querySelectorAll('.spatial-control input').forEach(el=>el.disabled=settings.model==='legacy');$('guide-legend').hidden=!settings.guides;updateOutputs();}
function selectMaterial(id,version=settings.materialVersion){Object.assign(settings,materialVersions[version].presets[id],{preset:id,materialPreset:id,materialVersion:version});syncUI();applyMaterial();dirtySurfaces();writeURL();notice(materialVersions[version].name+' · '+settings.name+' · 可继续微调');}
function applyMaterial(){mat.color.set(settings.color);for(const id of ['metalness','roughness','clearcoat','anisotropy'])mat[id]=settings[id];mat.wireframe=settings.wireframe;mat.needsUpdate=true;dirty=true;}
function fitScene(){
 if(modelBounds.isEmpty())return;
 const size=modelBounds.getSize(new T.Vector3()),center=modelBounds.getCenter(new T.Vector3()),phrase=glyph.generated&&glyph.charSources.length>1;
 if(phrase){group.position.set(-center.x,.28-modelBounds.min.y,0);target.set(0,group.position.y+center.y,0);}else{group.position.set(0,1.9,0);target.set(0,1.9,0);}
 const tangent=Math.tan(camera.fov*Math.PI/360);viewRadius=Math.max(8.4,(size.y*.5+.38)/tangent,(size.x*.5+.38)/(tangent*camera.aspect))+Math.max(0,size.z*.5-.5);
 controls.maxDistance=Math.max(24,viewRadius*2.3);
 const width=Math.max(4.65,size.x+1),height=Math.max(4.1,size.y+.7),back=Math.min(-1.18,modelBounds.min.z-.55);
 square.scale.set(width/4.65,height/4.65,1);square.position.set(0,target.y,back);circle.scale.set(width/4.6,1,height/4.6);circle.position.set(0,target.y,back);plinth.scale.set(width/4.8,1,1);plinth.position.set(0,.08,-.3);
 const extent=Math.max(5,size.x*.8,size.y*.8);Object.assign(key.shadow.camera,{left:-extent,right:extent,top:extent,bottom:-extent});key.shadow.camera.updateProjectionMatrix();applyLighting();dirty=true;
}
function applyLighting(){
 const dark=settings.background==='dark',color={stone:0xd8d8d8,dark:0x272d31,paper:0xece8dc}[settings.background];scene.background=new T.Color(color);scene.fog=new T.Fog(color,viewRadius+9,viewRadius+40);$('stage').classList.toggle('dark',dark);
 const angle=settings.azimuth*Math.PI/180;key.target.position.copy(target);key.position.set(Math.sin(angle)*7,target.y+4.7,Math.cos(angle)*7);key.intensity=settings.keyPower;key.color.set(settings.lighting==='warm'?0xffd7a1:0xfffcf3);rim.position.set(4,target.y+3,-4);rim.color.set(settings.lighting==='warm'?0xffe4bd:0xd6e4fa);rim.intensity=settings.lighting==='rim'?3:settings.lighting==='warm'?1.1:1.4;hemisphere.intensity=settings.lighting==='rim'?.22:.6;
 if(settings.lighting.startsWith('reference'))key.position.set(Math.sin(angle)*4,target.y+10.5,Math.cos(angle)*4);
 scene.environment=settings.lighting==='reference-v9'?referenceEnvironmentV9.texture:settings.lighting==='reference'?referenceEnvironment.texture:environmentTarget.texture;
 scene.environmentIntensity=settings.environment;scene.environmentRotation.y=settings.lighting.startsWith('reference')?settings.azimuth*Math.PI/180:(settings.azimuth+35)*Math.PI/180;renderer.toneMappingExposure=settings.exposure;key.castShadow=settings.shadows;floor.visible=settings.shadows;boardMaterial.color.set(dark?0x626969:settings.background==='paper'?0xf3ecdd:0xecece5);circle.visible=settings.display==='circle';square.visible=settings.display==='square';dirty=true;
}
function rebuildGuides(){
 for(const line of [...guides.children]){guides.remove(line);line.geometry.dispose();}
 for(const item of items){item.guideLines=constructionCurves(item.spec,item.kind).map((points,index)=>{const line=new T.Line(new T.BufferGeometry().setFromPoints(points),guideMaterials[index]);line.renderOrder=5;guides.add(line);return line;});}
}
function shapeSummary(){
 const manual=items.filter(item=>item.spec.brush).length;
 const oldGuang=settings.model==='legacy'&&glyph.text.includes('广');
 $('shape-summary').textContent=settings.model==='legacy'?(oldGuang?'旧广 · 通用自动造型\n相同材质、镜头与书写进度':'初始造型 · 保持当前材质、视角和进度'):settings.model==='reference-v8'?'v8 · 上一轮曲面\n当前材质、视角与进度保持':settings.model==='spatial'&&modelReport.transfers?.length?'v11 · 第二笔回卷接第三笔\n右下铺面 → 内缘上挑 → 移锋落笔':settings.model==='reference-v10'?'v10 · 内撇接虫\n保留上一版，供同角度对照':settings.model==='reference-v9'?'v9 · 分段接笔\n各段独立完成，再接下一段':modelReport.continuousRuns?.length?'v10 · 一条曲面连续生长\n同一前沿翻转 · 回锋不重新起笔':modelReport.strokeLinks?.some(l=>l.type==='temporal-gesture')?'虫左侧越过外撇\n单侧铺锋与前后穿插':modelReport.strokeLinks?.length?'收锋回带，再落锋入笔':manual?`逐笔重塑 · ${manual} 笔宽面与圆边\n保留手工铺锋和截面翻转`:`空间塑形 · ${modelReport.regions} 处交叠区域\n${glyph.modeling?.automatic?'含通用自动字形，未逐笔精修':'保留已有逐笔字势'}`;
 $('model-v10-option').hidden=!glyph.referenceV10Strokes;$('trajectory-row').hidden=!penTransfers.length;$('model-v8-option').hidden=!glyph.referenceV8Strokes;$('model-v9-option').hidden=!glyph.referenceV8Strokes;
 $('glyph-style-note').hidden=!glyph.text;$('glyph-style-note').textContent=glyph.modeling?.cursive?'草书重写 · '+glyph.charSources.filter(s=>s.cursive).map(s=>s.character).join('、')+(glyph.charSources.some(s=>!s.cursive)?'；其余沿用已有字形。':''):(settings.glyphStyle==='original'?'原有字形':'当前文字沿用已有字形。');
 if(glyph.modeling?.cursive)$('shape-summary').textContent='草书重写 · '+glyph.modeling.cursive+' 字\n整段回环连续成形 · 保留自然断连';
 if(modelReport.brushPlan?.inferredStrokes)$('shape-summary').textContent+='\n动态笔锋 · '+modelReport.brushPlan.inferredStrokes+' 笔推断运笔';
 $('stage-note').textContent=glyph.subtitle+' · '+(oldGuang?'旧广为通用自动造型':glyph.modeling?.label||'逐笔设计');
 $('model-info').textContent=(glyph.charSources?.length>1?glyph.charSources.length+' 字 · ':'')+items.length+' 段 · '+(modelReport.continuousRuns?.length?'连续生长':modelReport.sectionJoins?.length?'分段相接':modelReport.strokeLinks?.length?'连续笔势':settings.model==='spatial'?'空间塑形':'上一版造型');
 $('connection-row').hidden=!items.some(item=>item.spec.joinable);
 $('shape-summary').dataset.report=JSON.stringify(modelReport);$('resolved-text').textContent='输出 · '+glyph.text;
}
function rebuildSpecs(){
 if(!glyph.text){shapeDirty=false;dirty=true;return;}
 const next=prepareSpatialModel(glyph,settings),bounds=new T.Box3();
 const visibility=new Map(items.flatMap(item=>item.sourceIndices.map(index=>[index,item.enabled]))),resolution=part=>meshResolution(part,glyph.strokes.length,glyph.charSources?.length>1);
 if(next.parts.length!==items.length||next.parts.some((part,i)=>{const r=resolution(part);return items[i].g.userData.L!==r.L||items[i].g.userData.R!==r.R;})){
  for(const item of items){group.remove(item.mesh);item.g.dispose();}items=makeItems(next,glyph,bounds);for(const item of items){item.enabled=item.sourceIndices.some(index=>visibility.get(index)!==false);group.add(item.mesh);}
 }else for(let i=0;i<items.length;i++){const item=items[i],part=next.parts[i];item.s=part.stroke;item.sourceIndices=part.sourceIndices;item.spec=part.spec;item.kind=part.kind;updateVolume(item.g,item.spec,item.kind,1,settings.ridges,settings.writing);bounds.union(item.g.boundingBox);item.last=-1;}
 $('writing-row').hidden=!items.some(item=>item.spec.gesture);
 modelReport=next.report;penTransfers=next.transfers||[];rebuildTransferGuide();modelBounds.copy(bounds);rebuildGuides();shapeSummary();renderStrokeControls();shapeDirty=false;dirty=true;
}
function meshResolution(part,segments,phrase=false){const base=part.spec.brush&&segments<=40?(phrase?200:300):segments>40?110:phrase?170:220;return {L:Math.round(base*(part.spec.longitudinalScale||1)),R:part.spec.brush&&segments<=40?(phrase?72:96):segments>40?48:72};}
function makeItems(constructed,next,bounds){
 const prepared=[];
 try{constructed.parts.forEach(({stroke:s,kind,spec,sourceIndices},i)=>{const {L,R}=meshResolution({spec},next.strokes.length,next.charSources?.length>1),g=createVolume(L,R);updateVolume(g,spec,kind,1,settings.ridges,settings.writing);if(!g.attributes.position.array.every(Number.isFinite))throw Error('该字的曲面暂时无法构建。');bounds.union(g.boundingBox);const mesh=new T.Mesh(g,mat);mesh.castShadow=true;mesh.receiveShadow=true;mesh.frustumCulled=false;prepared.push({s,i,kind,g,mesh,spec,sourceIndices,last:1,enabled:true});});}catch(error){prepared.forEach(item=>item.g.dispose());throw error;}return prepared;
}
function renderStrokeControls(){
 $('strokes').replaceChildren();items.forEach(item=>{const row=document.createElement('div');row.className='stroke-row';const checkbox=document.createElement('input');checkbox.type='checkbox';checkbox.checked=item.enabled;checkbox.setAttribute('aria-label','显示 '+item.s.name);checkbox.onchange=()=>{item.enabled=checkbox.checked;dirty=true;};const b=document.createElement('button');b.textContent=(item.i+1)+' '+item.s.name;b.dataset.stroke=item.i;b.onclick=()=>{seamPlayback=null;time=item.s.end;paused=true;updateButtons();dirty=true;};row.append(checkbox,b);$('strokes').append(row);});
}
function dirtySurfaces(){for(const item of items)item.last=-1;dirty=true;}
function writeURL(){
 const url=new URL(location.href);url.search='';if(glyph.text)url.searchParams.set('text',glyph.inputText||glyph.text);url.searchParams.set('script',settings.writingScript);if(settings.glyphStyle!=='cursive')url.searchParams.set('style',settings.glyphStyle);url.searchParams.set('material',settings.materialPreset);if(settings.materialVersion!=='classic')url.searchParams.set('surface',settings.materialVersion);if(lastYang!=='01')url.searchParams.set('variant',lastYang);if(settings.model!=='spatial')url.searchParams.set('model',settings.model);history.replaceState(null,'',url);
}
function updateButtons(){
 const hasGlyph=!!glyph.text;
 for(const id of ['pause','replay','timeline','speed','front','quarter','side','back','complete','reset','turntable','save-image','save-animation','export-model','save-settings'])$(id).disabled=!hasGlyph||building;
$('pause').innerHTML=icons[paused?'play':'pause'];$('pause').setAttribute('aria-label',paused?'继续书写':'暂停书写');$('pause').title=paused?'继续书写':'暂停书写';$('pause').setAttribute('aria-pressed',String(!paused));$('turntable').setAttribute('aria-pressed',String(spinning));$('seam-replay').setAttribute('aria-pressed',String(!!seamPlayback));}
function sourcePanel(){
 const src=glyph.source;$('source-name').textContent=src.name;$('source-phrase').textContent=src.phrase;$('source-link').href=src.url;$('source-link').hidden=!src.url;$('description').textContent=src.description;
 $('reference-image').closest('figure').hidden=!src.image;if(src.image){$('reference-image').src=src.image;$('reference-image').alt=src.name;}$('reference-caption').textContent=src.caption;
 $('source-list').replaceChildren();if(glyph.charSources?.length>1)for(const source of glyph.charSources){const link=document.createElement('a');link.textContent=source.name+' ↗';link.href=source.url;link.target='_blank';link.rel='noreferrer';$('source-list').append(link);}
 $('model-download').hidden=true;$('model-download').removeAttribute('href');
}
function installGlyph(next,complete=false){
 seamPlayback=null;if(settings.model.startsWith('reference-v')&&!next.referenceV8Strokes){settings.model='spatial';$('model').value=settings.model;}
 const bounds=new T.Box3();
 const constructed=prepareSpatialModel(next,settings);
 const prepared=makeItems(constructed,next,bounds);
 for(const item of items){group.remove(item.mesh);item.g.dispose();}glyph=next;items=prepared;for(const item of items)group.add(item.mesh);modelBounds.copy(bounds);if(glyph.text==='楊'&&!glyph.generated)lastYang=glyph.id;
 time=complete?duration():0;paused=complete;follow=true;spinning=false;controls.autoRotate=false;controls.enableDamping=false;controls.update();settings.explode=0;shapeDirty=false;$('explode').value=0;updateOutputs();fitScene();
 $('timeline').max=duration();$('variants').hidden=!glyph.text.includes('楊');$('hook-detail').hidden=glyph.text!=='風';$('seam-replay').hidden=glyph.text!=='風';$('writing-row').hidden=!items.some(item=>item.spec.gesture);document.querySelectorAll('[data-char]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.char===glyph.text)));document.querySelectorAll('[data-variant]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.variant===lastYang)));
 modelReport=constructed.report;penTransfers=constructed.transfers||[];rebuildTransferGuide();rebuildGuides();shapeSummary();sourcePanel();$('version-title').textContent=glyph.text+' · '+glyph.title;
 renderStrokeControls();writeURL();updateButtons();dirty=true;
}
function setBuilding(value,text=''){building=value;$('generate-text').disabled=value;$('save-animation').disabled=value;$('text-form').setAttribute('aria-busy',String(value));$('generate-text').textContent=value?'构形中…':'书写';$('loading').hidden=!value;$('loading').textContent=text||'正在构形…';updateButtons();}
async function generateText(value,complete=false){
 const revision=++buildRevision;
 try{const original=cleanText(value),script=settings.writingScript;setBuilding(true,'正在准备字形…');const text=cleanText(await convertScript(original,script));feedback('正在构建「'+text+'」…');setBuilding(true,'正在构形 · '+text);await new Promise(resolve=>requestAnimationFrame(resolve));const next=await createTextGlyph(text,{variantId:lastYang,style:settings.glyphStyle});if(revision!==buildRevision)return;next.inputText=original;next.inputScript=script;installGlyph(next,complete);$('text-input').value=original;$('resolved-text').textContent='输出 · '+next.text;feedback((text===next.text?'':text+' → ')+next.text+' · '+(next.modeling?.label||'逐笔设计')+' · '+duration().toFixed(0)+' 秒');if(params.get('看')==='回锋'&&glyph.text==='風')playSeam();}
 catch(error){if(revision===buildRevision)feedback(error.message+' 当前画面已保留。',true);}finally{if(revision===buildRevision)setBuilding(false);}
}
function selectKnown(id,complete=false){++buildRevision;setBuilding(false);installGlyph(catalog.find(g=>g.id===id)||catalog[0],complete);$('text-input').value=glyph.text;feedback('本地常用字库 · 1–8 个汉字');}
const smooth=(a,b,t)=>T.MathUtils.smoothstep(t,a,b);
function shot(t){const mix=smooth(0,glyph.writeEnd,t),finish=smooth(glyph.writeEnd,glyph.frontalAt,t),yaw=T.MathUtils.lerp(-.24,.16,mix)*(1-finish),radius=viewRadius+.12*(1-finish);controls.minDistance=4.8;controls.enableDamping=false;controls.target.copy(target);camera.position.set(Math.sin(yaw)*radius,target.y+.15*(1-finish),Math.cos(yaw)*radius);controls.update();}
function render(){
 if(!glyph.text){transferGuides.visible=false;displayGroup.visible=false;renderer.render(scene,camera);$('clock').textContent='0.00 / 0.00';$('timeline').value=0;$('view-label').textContent='';$('status').textContent='';return;}

 let current=-1;
 for(const item of items){const raw=T.MathUtils.clamp((time-item.s.start)/(item.s.end-item.s.start),0,1),p=writingProgress(item.spec,raw,settings.writing);item.mesh.visible=item.enabled&&p>.0001;if(item.mesh.visible&&item.last!==p){updateVolume(item.g,item.spec,item.kind,p,settings.ridges,settings.writing);item.last=p;}item.mesh.position.set((item.i-(items.length-1)/2)*.020*settings.explode,(item.i%3-1)*.08*settings.explode,(item.i-(items.length-1)/2)*.23*settings.explode);for(const line of item.guideLines||[]){line.visible=settings.guides&&item.mesh.visible;line.position.copy(item.mesh.position);line.geometry.setDrawRange(0,Math.max(2,Math.floor(p*120)+1));}if(raw>0)current=item.i;}
 updateTransferGuide();if(follow)shot(time);displayGroup.visible=settings.display!=='plain'&&camera.position.z>-.15;renderer.render(scene,camera);$('clock').textContent=time.toFixed(2)+' / '+duration().toFixed(2);$('timeline').value=time;$('view-label').textContent=recording?'保存动画中':seamPlayback?'第二→第三笔 · ¼×循环':spinning?'环绕查看':follow?(time>=glyph.frontalAt?'正面落幅':'轻微运镜'):'自由视角';
 const air=penTransfers.find(p=>time>=p.start&&time<p.end),active=items[Math.max(0,current)],phase=settings.writing==='flow'?writingPhase(active.spec,writingProgress(active.spec,T.MathUtils.clamp((time-active.s.start)/(active.s.end-active.s.start),0,1),settings.writing)):'';
 $('status').textContent=air?'二→三接笔 · 提锋移向第三笔落点':time<glyph.writeStart?'起笔':time<glyph.writeEnd?`正在写 · ${active.s.name}${phase?' · '+phase:''}`:time<glyph.frontalAt&&follow?'收笔 · 镜头回正':`${glyph.text} · ${follow?'正面停留':'成字查看'}`;document.querySelectorAll('[data-stroke]').forEach((b,i)=>b.setAttribute('aria-current',String(i===current)));
}
function stopSpin(){spinning=false;controls.autoRotate=false;updateButtons();}
function fixed(yaw,rise=0){follow=false;stopSpin();controls.minDistance=4.8;controls.enableDamping=false;controls.update();controls.target.copy(target);camera.position.set(Math.sin(yaw)*viewRadius,target.y+rise*viewRadius,Math.cos(yaw)*viewRadius);controls.update();dirty=true;}
controls.addEventListener('change',()=>dirty=true);controls.addEventListener('start',()=>{follow=false;stopSpin();controls.enableDamping=true;dirty=true;});
let composing=false;$('text-input').oncompositionstart=()=>composing=true;$('text-input').oncompositionend=()=>composing=false;
$('text-form').onsubmit=e=>{e.preventDefault();if(!composing&&!recording&&!building)generateText($('text-input').value);};
document.querySelectorAll('[data-char]').forEach(b=>b.onclick=()=>generateText(b.dataset.char,!!glyph.text&&paused&&time>=duration()));
document.querySelectorAll('[data-text]').forEach(b=>b.onclick=()=>{if(!recording&&!building){$('text-input').value=b.dataset.text;generateText(b.dataset.text);}});
document.querySelectorAll('[data-variant]').forEach(b=>b.onclick=()=>{const complete=!!glyph.text&&paused&&time>=duration();lastYang=b.dataset.variant;if(glyph.generated&&glyph.text.includes('楊'))generateText(glyph.inputText,complete);else generateText($('text-input').value,complete);});
$('replay').onclick=()=>{seamPlayback=null;time=0;paused=false;follow=true;stopSpin();settings.explode=0;$('explode').value=0;updateOutputs();updateButtons();dirty=true;};$('complete').onclick=()=>{seamPlayback=null;time=duration();paused=true;follow=true;stopSpin();updateButtons();dirty=true;};
 $('wind-reference-preset').onclick=()=>{settings={...defaults,...windReferencePreset};const url=new URL(location.href);url.searchParams.set('校准','風11');history.replaceState(null,'',url);selectKnown('feng',true);syncUI();applyMaterial();applyLighting();notice('風 v11 · 第二笔右下钩面向上回卷，再移锋承接第三笔。点“二→三慢放”查看。');};
$('pause').onclick=()=>{if(time>=duration()){time=0;paused=false;follow=true;stopSpin();}else paused=!paused;updateButtons();dirty=true;};$('timeline').oninput=e=>{seamPlayback=null;time=+e.target.value;paused=true;updateButtons();dirty=true;};$('speed').onchange=e=>speed=+e.target.value;
$('seam-replay').onclick=playSeam;
function playSeam(){
 const main=glyph.strokes.find(s=>s.role==='wind-main'),inner=glyph.strokes.find(s=>s.role==='wind-inner');if(!main||!inner)return;
 seamPlayback={start:main.start+(main.end-main.start)*.48,end:inner.start+(inner.end-inner.start)*.47};time=seamPlayback.start;paused=false;speed=.25;$('speed').value='.25';follow=false;stopSpin();
 const box=new T.Box3();for(const item of items.filter(item=>item.s.role==='wind-main'||item.s.role==='wind-inner'))for(const line of constructionCurves(item.spec,item.kind))for(const point of line)box.expandByPoint(point.clone().add(group.position));
 const center=box.getCenter(new T.Vector3()),size=box.getSize(new T.Vector3()),tan=Math.tan(camera.fov*Math.PI/360),distance=Math.max(3.4,(size.y*.5+.28)/tan,(size.x*.5+.28)/(tan*camera.aspect))+size.z*.5;
 controls.enableDamping=false;controls.update();controls.minDistance=1.25;controls.target.copy(center);camera.position.copy(center).add(new T.Vector3(Math.sin(.12)*distance,.035*distance,Math.cos(.12)*distance));controls.update();updateButtons();dirty=true;notice('二→三慢放 · ¼×循环。看右下钩面回卷，再移锋落入第三笔；笔势面板可显示运笔轨迹、切回v10对照。');
}
$('front').onclick=()=>fixed(0);$('quarter').onclick=()=>fixed(.54,.09);$('side').onclick=()=>fixed(Math.PI/2);$('back').onclick=()=>fixed(Math.PI);$('reset').onclick=()=>{follow=true;stopSpin();dirty=true;};canvas.ondblclick=()=>$('reset').click();
$('hook-detail').onclick=()=>{
 const item=items.find(item=>item.s.role==='wind-main'||/横折弯钩/.test(item.s.name));if(!item)return;
 seamPlayback=null;time=duration();paused=true;follow=false;stopSpin();controls.enableDamping=false;controls.update();render();
 const box=new T.Box3(),{L,R}=item.g.userData,p=item.g.attributes.position;
 for(let j=Math.floor(L*.72);j<L;j++)for(let k=0;k<R;k++){const at=1+(j-1)*R+k;box.expandByPoint(new T.Vector3(p.getX(at),p.getY(at),p.getZ(at)).add(item.mesh.position).add(group.position));}
 const center=box.getCenter(new T.Vector3()),size=box.getSize(new T.Vector3()),tan=Math.tan(camera.fov*Math.PI/360),distance=Math.max(1.8,(size.y*.5+.15)/tan,(size.x*.5+.15)/(tan*camera.aspect))+size.z*.35;
 controls.minDistance=1.25;controls.target.copy(center);camera.position.copy(center).add(new T.Vector3(Math.sin(.15)*distance,.04*distance,Math.cos(.15)*distance));controls.update();updateButtons();notice('右下收笔特写 · 可旋转，也可在此视角切换新旧模型。点“正面”回到整字。');dirty=true;
};
$('turntable').onclick=()=>{spinning=!spinning;follow=false;controls.autoRotate=spinning;controls.autoRotateSpeed=.75;controls.enableDamping=true;updateButtons();dirty=true;};$('fullscreen').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await $('stage').requestFullscreen();}catch{notice('当前环境不支持全屏，可用浏览器放大查看。');}};
for(const id of Object.keys(materialPresets)){const b=document.createElement('button');b.className='preset';b.dataset.preset=id;const swatch=document.createElement('i'),label=document.createElement('span');swatch.setAttribute('aria-hidden','true');b.append(swatch,label);b.onclick=()=>selectMaterial(id);$('presets').append(b);}
$('materialVersion').onchange=e=>selectMaterial(settings.materialPreset,e.target.value);
$('writing').onchange=e=>{settings.writing=e.target.value;rebuildSpecs();writeURL();notice(settings.writing==='flow'?'动态运笔 · 铺锋、提按与翻转':'逐段显露 · 相同字形与运镜');};
$('connection').onchange=e=>{settings.connection=e.target.value;rebuildSpecs();syncUI();writeURL();notice(settings.connection==='linked'?'第二笔回卷 → 第三笔承势 · 单侧铺面':'逐笔查看 · 相同镜头与书写进度');};
for(const id of ['color','metalness','roughness','clearcoat','anisotropy'])$(id).oninput=e=>{settings[id]=id==='color'?e.target.value:+e.target.value;settings.preset='custom';syncUI();applyMaterial();};$('ridges').oninput=e=>{settings.ridges=+e.target.value;settings.preset='custom';syncUI();dirtySurfaces();};
for(const id of ['fullness','depth','turn','layering','harmony'])$(id).oninput=e=>{settings[id]=+e.target.value;shapeDirty=true;updateOutputs();};$('explode').oninput=e=>{settings.explode=+e.target.value;updateOutputs();dirty=true;};
for(const id of ['lighting','background','display','azimuth','keyPower','environment','exposure'])$(id).oninput=e=>{settings[id]=id in enums?e.target.value:+e.target.value;updateOutputs();applyLighting();};$('shadows').onchange=e=>{settings.shadows=e.target.checked;applyLighting();};$('wireframe').onchange=e=>{settings.wireframe=e.target.checked;applyMaterial();};
$('model').onchange=e=>{settings.model=e.target.value;rebuildSpecs();syncUI();writeURL();notice('模型已切换，当前视角和书写进度已保留。');};$('guides').onchange=e=>{settings.guides=e.target.checked;$('guide-legend').hidden=!settings.guides;dirty=true;};
$('trajectory').onchange=e=>{settings.trajectory=e.target.checked;dirty=true;notice(settings.trajectory?'棕色虚线与圆点是二→三运笔辅助线，可关闭；不属于成字模型。':'已隐藏运笔辅助线');};
$('show-all').onclick=()=>{items.forEach(i=>i.enabled=true);$('strokes').querySelectorAll('input').forEach(i=>i.checked=true);dirty=true;};
const tabButtons=[...document.querySelectorAll('[data-panel]')];function panel(id){tabButtons.forEach(b=>{const active=b.dataset.panel===id;b.setAttribute('aria-selected',String(active));b.tabIndex=active?0:-1;$('panel-'+b.dataset.panel).hidden=!active;});document.querySelector('.panel-scroll').scrollTop=0;}
tabButtons.forEach((b,i)=>{b.onclick=()=>panel(b.dataset.panel);b.onkeydown=e=>{if(['ArrowLeft','ArrowRight','Home','End'].includes(e.key)){e.preventDefault();const n=e.key==='Home'?0:e.key==='End'?3:(i+(e.key==='ArrowRight'?1:3))%4;panel(tabButtons[n].dataset.panel);tabButtons[n].focus();}};});
function snapshot(){return {format:'volumetric-calligraphy-studio',version:4,glyphId:glyph.id,inputText:glyph.generated?glyph.inputText:null,yangVariant:lastYang,text:glyph.text,modeling:glyph.modeling||{sculpted:1,automatic:0,label:'逐笔设计'},spatialModel:modelReport,settings:{...settings},playback:{time,speed,duration:duration()},camera:{position:camera.position.toArray(),target:controls.target.toArray()},visible:items.map(i=>i.enabled),visibleBySource:Object.fromEntries(items.flatMap(item=>item.sourceIndices.map(index=>[index,item.enabled]))),source:glyph.source.url,sourceInfo:glyph.source,charSources:glyph.charSources||[],materialReference:'https://www.bilibili.com/video/BV16a4y1P7fA/'};}
function download(blob,name){const url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),30000);}
$('save-image').onclick=()=>{if(shapeDirty)rebuildSpecs();render();const name=`${glyph.text}-${glyph.title}-${settings.preset}.png`;canvas.toBlob(blob=>{if(blob){download(blob,name);notice('已保存当前视角画面 PNG');}else notice('画面保存失败，请重试。');},'image/png');};$('save-settings').onclick=()=>{download(new Blob([JSON.stringify(snapshot(),null,2)],{type:'application/json'}),`${glyph.text}-调色.json`);notice('已保存输入文字、调色、体量、进度与镜头');};$('load-settings').onclick=()=>$('settings-file').click();
$('settings-file').onchange=async e=>{
 const file=e.target.files[0];if(!file)return;const revision=++buildRevision;
 try{
  if(file.size>2000000)throw Error('文件过大');const data=JSON.parse(await file.text());if(data.format!=='volumetric-calligraphy-studio'||![1,2,3,4].includes(data.version))throw Error('格式不匹配');const variant=['01','02','03'].includes(data.yangVariant)?data.yangVariant:lastYang;
  let nextGlyph;if(data.inputText){setBuilding(true);nextGlyph=await createTextGlyph(await convertScript(data.inputText,data.settings?.writingScript||'traditional'),{variantId:variant,style:data.settings?.glyphStyle||'cursive'});nextGlyph.inputText=data.inputText;}else nextGlyph=catalog.find(g=>g.id===data.glyphId);if(!nextGlyph)throw Error('未找到此字形');if(revision!==buildRevision)return;
  const incoming=data.settings||{},next={...defaults};if(data.version<3)next.model='legacy';for(const [id,[lo,hi]] of Object.entries(numeric))if(Number.isFinite(incoming[id]))next[id]=T.MathUtils.clamp(incoming[id],lo,hi);for(const [id,choices] of Object.entries(enums))if(choices.includes(incoming[id]))next[id]=incoming[id];if(/^#[0-9a-f]{6}$/i.test(incoming.color))next.color=incoming.color;for(const id of ['shadows','wireframe','guides','trajectory'])if(typeof incoming[id]==='boolean')next[id]=incoming[id];next.preset=Object.hasOwn(materialPresets,incoming.preset)?incoming.preset:'custom';
  if(data.spatialModel?.revision==='boundary-volume-v8-20261024'&&incoming.model==='spatial'&&nextGlyph.referenceV8Strokes)next.model='reference-v8';
  if(data.spatialModel?.revision==='boundary-volume-v9-20261024'&&incoming.model==='spatial'&&nextGlyph.referenceV8Strokes)next.model='reference-v9';
  if(data.spatialModel?.revision==='continuous-growth-v10-20261024'&&incoming.model==='spatial'&&nextGlyph.referenceV10Strokes)next.model='reference-v10';
  if(!enums.materialVersion.includes(incoming.materialVersion)){const keys=['color','metalness','roughness','clearcoat','anisotropy','ridges'];next.materialVersion=data.version<3||Object.values(classicMaterialPresets).some(p=>keys.every(key=>p[key]===incoming[key]))?'classic':'smooth';}
  const family=materialVersions[next.materialVersion].presets;next.materialPreset=Object.hasOwn(family,incoming.materialPreset)?incoming.materialPreset:next.preset!=='custom'?next.preset:Object.keys(family).find(key=>family[key].name===incoming.name)||'silver';next.name=family[next.materialPreset].name;
  settings=next;lastYang=variant;const savedExplode=settings.explode;installGlyph(nextGlyph,true);settings.explode=savedExplode;time=Number.isFinite(data.playback?.time)?T.MathUtils.clamp(data.playback.time,0,duration()):duration();speed=[.25,.5,1,2].includes(data.playback?.speed)?data.playback.speed:1;$('speed').value=String(speed).replace(/^0\./,'.');items.forEach((item,i)=>item.enabled=data.visibleBySource?item.sourceIndices.some(index=>data.visibleBySource[index]!==false):data.visible?.[i]!==false);$('strokes').querySelectorAll('input').forEach((el,i)=>el.checked=items[i].enabled);
  const validVec=a=>Array.isArray(a)&&a.length===3&&a.every(v=>Number.isFinite(v)&&Math.abs(v)<=200);if(validVec(data.camera?.position)&&validVec(data.camera?.target)){const pos=new T.Vector3(...data.camera.position),at=new T.Vector3(...data.camera.target);if(pos.distanceTo(at)>=1.25&&pos.distanceTo(at)<=controls.maxDistance){follow=false;controls.minDistance=pos.distanceTo(at)<4.8?1.25:4.8;controls.enableDamping=false;controls.update();camera.position.copy(pos);controls.target.copy(at);controls.update();}}
  if(data.inputText)$('text-input').value=data.inputText;syncUI();applyMaterial();applyLighting();updateButtons();dirty=true;notice('文字、调色、笔势与镜头已载入，停在保存的进度。');
 }catch(error){notice('无法载入：'+error.message);}finally{if(revision===buildRevision)setBuilding(false);e.target.value='';}
};
$('export-model').onclick=async()=>{
 if(shapeDirty)rebuildSpecs();render();if(!items.some(i=>i.mesh.visible)){notice('当前没有可见笔画，请先播放或点击“看成字”。');return;}const button=$('export-model');button.disabled=true;notice('正在打包当前可见曲面…');await new Promise(resolve=>requestAnimationFrame(resolve));
 try{const capturedGlyph=glyph,metadata=snapshot(),files=modelFiles(items,mat,metadata),sources=capturedGlyph.charSources||[capturedGlyph.source];files['SOURCE.txt']=sources.map(src=>[src.name,src.phrase,src.url,src.caption,src.description].join('\n')).join('\n\n')+'\n\n体量、深度与截面为本项目重建。材质参考：https://www.bilibili.com/video/BV16a4y1P7fA/';if(capturedGlyph.requiresLicense||capturedGlyph.text==='天'){const license=await fetch('data/ARPHICPL.TXT');if(!license.ok)throw Error('字形许可文件未能载入');files['ARPHICPL.TXT']=await license.text();}download(zipStore(files),`${capturedGlyph.text}-${capturedGlyph.title}-当前模型.zip`);notice('已导出 OBJ、MTL 和参数；包含当前进度与可见笔画。');}catch(error){notice('导出失败：'+error.message);}finally{button.disabled=false;}
};
$('restore').onclick=()=>{settings={...defaults,writingScript:settings.writingScript,glyphStyle:settings.glyphStyle};syncUI();rebuildSpecs();applyMaterial();applyLighting();items.forEach(i=>i.enabled=true);$('strokes').querySelectorAll('input').forEach(i=>i.checked=true);speed=1;$('speed').value='1';follow=true;stopSpin();writeURL();notice('已恢复默认材质、体量、布光与运镜');};
function finishRecording(capture,error=null){
 if(recording!==capture)return;recording=null;seamPlayback=capture.saved.seamPlayback;capture.stream.getTracks().forEach(track=>track.stop());capture.locks.forEach(([el,disabled])=>el.disabled=disabled);controls.enabled=true;
 time=capture.saved.time;paused=capture.saved.paused;follow=capture.saved.follow;spinning=capture.saved.spinning;settings.explode=capture.saved.explode;controls.autoRotate=spinning;controls.enableDamping=false;controls.update();camera.position.copy(capture.saved.position);controls.target.copy(capture.saved.target);controls.update();syncUI();updateButtons();$('save-animation').innerHTML='保存书写动画 <span>WebM</span>';$('save-animation').setAttribute('aria-pressed','false');dirty=true;
 if(error||!capture.chunks.length){notice('动画保存失败：'+(error?.message||'编码器没有返回画面'));return;}download(new Blob(capture.chunks,{type:capture.recorder.mimeType}),capture.text+(capture.range?'-回锋慢放.webm':'-立体书写.webm'));notice('已保存 '+capture.elapsed.toFixed(1)+' 秒 WebM 动画。');
}
$('save-animation').onclick=()=>{
 if(recording){if(recording.recorder.state!=='inactive')recording.recorder.stop();return;}if(!window.MediaRecorder||!canvas.captureStream){notice('当前浏览器不支持 WebM 保存，可直接使用在线书写动画。');return;}
 let stream;
 try{
  stream=canvas.captureStream(30);const mimeType=['video/webm;codecs=vp9','video/webm;codecs=vp8','video/webm'].find(type=>MediaRecorder.isTypeSupported(type));if(!mimeType)throw Error('缺少 WebM 编码器');
  const recorder=new MediaRecorder(stream,{mimeType,videoBitsPerSecond:9000000}),capture={recorder,stream,chunks:[],text:glyph.text,start:0,elapsed:0,finishing:false,range:seamPlayback?{...seamPlayback,speed}:null,duration:seamPlayback?(seamPlayback.end-seamPlayback.start)/speed:duration(),saved:{time,paused,follow,spinning,seamPlayback,explode:settings.explode,position:camera.position.clone(),target:controls.target.clone()},locks:[]};capture.locks=[...document.querySelectorAll('button,input,select')].filter(el=>el!==$('save-animation')).map(el=>[el,el.disabled]);capture.locks.forEach(([el])=>el.disabled=true);
  recorder.ondataavailable=e=>{if(e.data.size)capture.chunks.push(e.data);};recorder.onstop=()=>finishRecording(capture);recorder.onerror=e=>finishRecording(capture,e.error||Error('编码器出错'));
  recording=capture;controls.enabled=false;controls.autoRotate=false;spinning=false;seamPlayback=null;follow=!capture.range;paused=false;time=capture.range?.start||0;settings.explode=0;$('explode').value=0;render();capture.start=performance.now();recorder.start(500);$('save-animation').textContent='停止并保存';$('save-animation').setAttribute('aria-pressed','true');notice('正在保存书写动画，请保持本页打开…');dirty=true;
 }catch(error){stream?.getTracks().forEach(track=>track.stop());if(recording)finishRecording(recording,error);else notice('动画保存失败：'+error.message);}
};
canvas.onkeydown=e=>{if(e.code==='Space'&&!recording){e.preventDefault();$('pause').click();}};
function resize(){const w=Math.max(1,canvas.clientWidth),h=Math.max(1,canvas.clientHeight),scale=Math.min(renderScale,2400/w,2000/h);renderer.setSize(Math.round(w*scale),Math.round(h*scale),false);camera.aspect=w/h;camera.updateProjectionMatrix();if(glyph)fitScene();dirty=true;}new ResizeObserver(resize).observe(canvas);resize();
const params=new URL(location.href).searchParams;for(const [a,b] of [['text','文'],['material','材质'],['surface','材质版'],['model','模型'],['variant','版']])if(params.has(a))params.set(b,params.get(a));if(['simplified','traditional','original'].includes(params.get('script')))settings.writingScript=params.get('script');if(enums.glyphStyle.includes(params.get('style')))settings.glyphStyle=params.get('style');const initialPreset=params.get('材质'),calibration=params.get('校准'),hasCalibration=['風8','風9','風10','風11'].includes(calibration);
if(calibration==='風8')Object.assign(settings,windReferencePresetV8,{model:'reference-v8'});
if(calibration==='風9'||calibration==='風10'||calibration==='風11')Object.assign(settings,windReferencePreset);
if(params.get('接笔')==='separate')settings.connection='separate';
if(params.get('运笔')==='reveal')settings.writing='reveal';
if(enums.materialVersion.includes(params.get('材质版')))settings.materialVersion=params.get('材质版');
if(Object.hasOwn(materialPresets,initialPreset)&&!(hasCalibration&&initialPreset==='silver'&&settings.materialVersion==='smooth'))Object.assign(settings,materialVersions[settings.materialVersion].presets[initialPreset],{preset:initialPreset,materialPreset:initialPreset});
else if(!hasCalibration)Object.assign(settings,materialVersions[settings.materialVersion].presets.ink);
if(enums.model.includes(params.get('模型')))settings.model=calibration==='風8'&&params.get('v')!=='wind9'&&params.get('模型')==='spatial'?'reference-v8':params.get('模型');
if(calibration==='風10'&&params.get('v')!=='wind11'&&settings.model==='spatial')settings.model='reference-v10';
if(enums.lighting.includes(params.get('灯光')))settings.lighting=params.get('灯光');
lastYang=['01','02','03'].includes(params.get('版'))?params.get('版'):'01';
$('text-input').value='';$('timeline').max=0;$('variants').hidden=true;$('hook-detail').hidden=true;$('seam-replay').hidden=true;$('writing-row').hidden=true;$('connection-row').hidden=true;
$('resolved-text').textContent='';$('shape-summary').textContent='输入文字后查看笔势。';$('source-name').textContent='';sourcePanel();syncUI();applyMaterial();applyLighting();panel('material');$('loading').hidden=true;updateButtons();writeURL();
let last=performance.now();function loop(now){const dt=Math.min(.25,Math.max(0,(now-last)/1000));last=now;if(shapeDirty)rebuildSpecs();if(!follow)controls.update(dt);if(recording){recording.elapsed=Math.min(recording.duration,Math.max(0,(now-recording.start)/1000));time=recording.range?recording.range.start+recording.elapsed*recording.range.speed:recording.elapsed;dirty=true;}else if(!paused){time=Math.min(seamPlayback?.end||duration(),time+dt*speed);dirty=true;if(seamPlayback&&time>=seamPlayback.end){time=seamPlayback.start;}else if(time>=duration()){paused=true;updateButtons();}}if(spinning)dirty=true;if(dirty){dirty=false;render();}if(recording&&recording.elapsed>=recording.duration&&!recording.finishing){const capture=recording;capture.finishing=true;requestAnimationFrame(()=>{if(recording===capture&&capture.recorder.state!=='inactive')capture.recorder.stop();});}requestAnimationFrame(loop);}requestAnimationFrame(loop);



$('glyphStyle').onchange=async e=>{settings.glyphStyle=e.target.value;if($('text-input').value.trim())await generateText($('text-input').value);else writeURL();syncUI();};
$('writingScript').onchange=async e=>{settings.writingScript=e.target.value;if($('text-input').value.trim())await generateText($('text-input').value);else writeURL();syncUI();};
export function studioState(){return {text:glyph?.text,input:glyph?.inputText,script:settings.writingScript,paused,time,duration:duration(),recording:!!recording,building,settings:{...settings},camera:{position:camera.position.toArray(),target:controls.target.toArray()},segments:items.length};}
export function setQuality(value){const preset={draft:[.9,1024],balanced:[1.25,1536],high:[1.75,2048]}[value]||[1.25,1536];renderer.shadowMap.enabled=settings.shadows;key.shadow.mapSize.set(preset[1],preset[1]);key.shadow.map?.dispose();key.shadow.map=null;renderScale=preset[0];resize();dirty=true;}
