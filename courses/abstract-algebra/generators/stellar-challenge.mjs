import * as T from '../../../visuals/3d/vendor/three.module.js';
import {levels,minimumGenerators,generationRound} from './challenge-model.mjs';
import {createChallengeAudio} from './challenge-audio.mjs';
export function mountStellarChallenge({world,onPass,onExit,t}){
 const ui=document.createElement('section');ui.id='stellarChallenge';ui.hidden=true;ui.innerHTML=`<div class="challenge-heading"><span id="challengeSector"></span><div id="challengeSteps"></div><p id="challengeHint"></p></div><div id="celestialLabels"></div><div class="challenge-bottom"><div id="chosenStars"></div><button id="forgeStar" aria-label="开始生成"><span class="forge-rim"></span><strong></strong><small></small></button><span id="forgeStatus" role="status"></span></div><div id="challengeResult" role="status"><span></span><h2></h2><p></p></div><button id="challengeExit">←</button><button id="challengeSound" aria-label="音效">♪</button>`;document.body.append(ui);
 const $=id=>document.getElementById(id),audio=createChallengeAudio(),labels=[],births=new Map(),effects=[];
 let game=null,known=new Set(),seeds=new Set(),fixed=null,phase='select',elapsed=0,clock=0,queue=[],delay=0,start=0,sfx=true;
 const number=i=>i===game.group.e?'e':String(i<game.group.e?i+2:i+1);
 function message(zh,en){$('forgeStatus').textContent=t(zh,en);}
 function sync(){if(!game)return;if(world.challenge)world.challenge.selecting=phase==='select';const count=levels(game.group).length,left=game.level.budget-seeds.size;
 $('challengeSector').textContent=game.name;$('challengeSteps').textContent=Array.from({length:count},(_,i)=>i===game.stage?'◆':'◇').join('  ');
 $('challengeHint').textContent=game.level.preset?t('一颗星已亮，找到它的伙伴','One star is lit. Find its companions'):t('点亮起点，生成群星','Choose the first lights. Generate the stars');
 const b=$('forgeStar');b.disabled=phase!=='select'||seeds.size===0;b.querySelector('strong').textContent=phase==='generating'?`${known.size}/${game.group.table.length}`:String(left);b.querySelector('small').textContent=phase==='generating'?t('生成中','GENERATING'):t('造星 · 开始','IGNITE');b.dataset.phase=phase;
 b.setAttribute('aria-label',phase==='select'?t(`剩余 ${left} 次造星，开始生成`,`Start generation, ${left} choices remaining`):t('正在生成','Generating'));
 $('chosenStars').replaceChildren(...[...seeds].map(i=>{const b=document.createElement('button');b.textContent=number(i)+(i===fixed?' · ✦':'');b.disabled=i===fixed||phase!=='select';b.setAttribute('aria-label',t('取消起点 ','Remove seed ')+number(i));b.onclick=()=>pick(i);return b;}));
 for(const [i,b] of labels.entries()){b.setAttribute('aria-pressed',String(seeds.has(i)));b.dataset.lit=String(known.has(i));b.disabled=phase!=='select'||i===fixed;}
 }
 function pick(i){if(!game||phase!=='select'||i===fixed)return;if(seeds.has(i))seeds.delete(i);else if(seeds.size<game.level.budget){seeds.add(i);births.set(i,0);audio.sound('select');}else{message('造星次数已用完，可取消一个起点','No choices left. Remove a seed to change it.');return;}known=new Set(seeds);sync();}
 function clearEffects(){for(const e of effects){world.scene.remove(e.mesh);e.mesh.geometry.dispose();e.mesh.material.dispose();}effects.length=0;}
 function flash(a,b,c){const system=world.systems[world.selected],points=[a,b,c].map(i=>system.userData.planets[i].getWorldPosition(new T.Vector3()));const geometry=new T.BufferGeometry().setFromPoints([points[0],points[2],points[1],points[2]]),mesh=new T.LineSegments(geometry,new T.LineBasicMaterial({color:0xbadfff,transparent:true,opacity:.8,depthTest:false}));mesh.layers.set(1);world.scene.add(mesh);effects.push({mesh,age:0});}
 function beginStage(){phase='select';elapsed=0;queue=[];delay=0;births.clear();clearEffects();seeds=new Set();fixed=null;known=new Set();game.level=levels(game.group)[game.stage];
 if(game.level.preset){const pool=minimumGenerators(game.group).eligible;fixed=pool[Math.floor(Math.random()*pool.length)];seeds.add(fixed);known.add(fixed);}
 $('challengeResult').classList.remove('visible');$('challengeResult').setAttribute('aria-hidden','true');ui.dataset.phase=phase;message('选择天体后，按下造星核心','Choose celestial bodies, then press the core');start=performance.now();sync();
 }
 function finish(){phase=known.size===game.group.table.length?'success':'fail';ui.dataset.phase=phase;elapsed=0;const result=$('challengeResult');result.querySelector('span').textContent=phase==='success'?'✦':'✧';result.querySelector('h2').textContent=phase==='success'?t('众星归位','The stars align'):t('群星陨落','The stars fall');result.querySelector('p').textContent=phase==='success'?t('航道已点亮','A new passage opens'):t(`只生成了 ${known.size} / ${game.group.table.length} 个元素 · 重新选择`,`${known.size} / ${game.group.table.length} elements · Try another beginning`);result.classList.add('visible');result.setAttribute('aria-hidden','false');audio.sound(phase);
 if(phase==='success')onPass(game.key,game.stage,Math.round((performance.now()-start)/1000));sync();
 }
 $('forgeStar').onclick=()=>{if(!game||phase!=='select'||!seeds.size)return;phase='generating';ui.dataset.phase=phase;elapsed=0;queue=generationRound(game.group,known);delay=1.1;audio.sound('enter');sync();};
 function close(){if(!game)return;for(const p of world.systems[world.selected].userData.planets){p.scale.setScalar(p.userData.baseSize);p.userData.light.value=1;}clearEffects();game=null;world.challenge=null;ui.hidden=true;document.body.classList.remove('challenge-mode');document.getElementById('galaxyUI').inert=false;onExit();}
 $('challengeExit').onclick=close;$('challengeSound').onclick=()=>{sfx=!sfx;audio.setEnabled(sfx);$('challengeSound').setAttribute('aria-pressed',String(sfx));$('challengeSound').textContent=sfx?'♪':'♩';};
 function tick(dt){if(!game)return;clock+=dt;elapsed+=dt;for(const [i,age] of births)births.set(i,age+dt);
 if(phase==='generating'){delay-=dt;if(delay<=0){if(!queue.length&&[...births.values()].some(age=>age<1.05)){delay=.12;return;}if(!queue.length){queue=generationRound(game.group,known);if(!queue.length){finish();return;}}const event=queue.shift();known.add(event.c);births.set(event.c,0);flash(event.a,event.b,event.c);audio.sound('birth');message(`${number(event.a)} · ${number(event.b)} = ${number(event.c)}`,`${number(event.a)} · ${number(event.b)} = ${number(event.c)}`);delay=Math.max(.28,1.1-game.group.table.length*.006);sync();}}
 if(phase==='fail'&&elapsed>3.2)beginStage();if(phase==='success'&&elapsed>2.5){if(game.stage+1<levels(game.group).length){game.stage++;beginStage();audio.sound('enter');}else close();}
 for(let i=effects.length-1;i>=0;i--){const e=effects[i];e.age+=dt;e.mesh.material.opacity=Math.max(0,.75-e.age);if(e.age>1){world.scene.remove(e.mesh);e.mesh.geometry.dispose();e.mesh.material.dispose();effects.splice(i,1);}}
 }
 function pose(){if(!game)return;const system=world.systems[world.selected];for(const p of system.userData.planets){const i=p.userData.element,lit=known.has(i),age=births.get(i)??3,growth=lit?Math.min(1,.08+age/1.05):1;let scale=p.userData.baseSize*growth;
 p.userData.light.value+=( (lit?1:.18)-p.userData.light.value)*.12;
 if(phase==='fail'){const f=Math.min(1,elapsed/2.5);if(i===game.group.e){p.userData.light.value=1+.3*Math.sin(f*Math.PI);scale=p.userData.baseSize;}else if(lit){p.position.applyAxisAngle(new T.Vector3(0,1,0),-f*Math.PI*2.5).multiplyScalar(Math.pow(1-f,1.7));scale*=Math.pow(1-f,1.5);p.userData.light.value*=1-Math.pow(f,3);}else p.userData.light.value=.06;}

 p.scale.setScalar(Math.max(.001,scale));}}
 function project(){if(!game)return;const root=world.systems[world.selected];for(const [i,b] of labels.entries()){const v=root.userData.planets[i].getWorldPosition(new T.Vector3()).project(world.camera);b.style.left=(v.x*.5+.5)*world.w+'px';b.style.top=(-v.y*.5+.5)*world.h+'px';b.hidden=phase==='fail'||v.z>1||Math.abs(v.x)>1||Math.abs(v.y)>1;}}
 return {open(key,group,name,stage=0){game={key,group,name,stage:Math.min(stage,levels(group).length-1)};labels.length=0;$('celestialLabels').replaceChildren(...group.labels.map((label,i)=>{const b=document.createElement('button');b.className='celestial-label';b.textContent=number(i);b.title=`${number(i)} · ${label}`;b.setAttribute('aria-label',t('点亮天体 ','Light celestial body ')+number(i));b.onclick=()=>pick(i);labels.push(b);return b;}));ui.hidden=false;document.body.classList.add('challenge-mode');document.getElementById('galaxyUI').inert=true;world.challenge={pick,tick,pose,project};beginStage();audio.sound('enter');},close,sync};
}
