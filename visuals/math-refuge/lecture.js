import * as THREE from 'three';
import {LectureClock,boardHeights} from './lecture-state.js?v=3-coast';

const W=1536,H=640,BOARD_W=5.3,BOARD_H=2.05;
const phaseNames={lift:'升降换板',erase:'擦除板书',write:'粉笔书写',hold:'停留阅读'};
export async function createLecture(scene,renderer){
  const response=await fetch('./assets/chalk/pages.json?v=3-coast');
  if(!response.ok)throw new Error('Unable to load the spectral notebook');
  const {pages}=await response.json(),clock=new LectureClock(pages.length);
  const cache=new Map(),pending=new Map();let loadingError=null,version=0;
  function load(index){
    if(index<0)return Promise.resolve(null);
    if(cache.has(index))return Promise.resolve(cache.get(index));
    if(pending.has(index))return pending.get(index);
    const job=new Promise((resolve,reject)=>{
      const image=new Image();image.onload=()=>{
        cache.set(index,image);pending.delete(index);version++;
        // Retain six on-board pages and the active/next page, evict other SVGs.
        const keep=new Set([...clock.slots.map(s=>s.page),clock.page,(clock.page+1)%pages.length]);
        for(const key of cache.keys())if(cache.size>10&&!keep.has(key))cache.delete(key);
        resolve(image);
      };image.onerror=()=>{pending.delete(index);reject(new Error('板书资源加载失败，请刷新重试。'));};image.src=pages[index].asset;
    });pending.set(index,job);return job;
  }
  await load(0);
  const boards=[],mix=[0,0,0],targets=[0,0,0];let playing=true,accumulator=0;
  const frameMaterial=new THREE.MeshStandardMaterial({color:'#735c3e',roughness:.65});
  const metal=new THREE.MeshStandardMaterial({color:'#9caa9e',roughness:.32,metalness:.65});
  const wall=new THREE.Mesh(new THREE.BoxGeometry(17.2,4.8,.16),new THREE.MeshStandardMaterial({color:'#102421',roughness:1}));
  wall.position.set(28,2.65,-10.82);wall.name='Six-board lecture wall';scene.add(wall);
  const cube=new THREE.BoxGeometry(1,1,1);
  function part(parent,p,s,material){const mesh=new THREE.Mesh(cube,material);mesh.position.fromArray(p);mesh.scale.fromArray(s);parent.add(mesh);return mesh;}
  for(let pair=0;pair<3;pair++){
    const x=22.4+pair*5.6;
    for(const dx of [-2.76,2.76])part(scene,[x+dx,2.7,-10.6],[.045,4.75,.09],metal);
    for(let side=0;side<2;side++){
      const group=new THREE.Group();group.position.set(x,boardHeights(0)[side],-10.45+side*.16);
      group.name=`Sliding chalkboard ${pair+1}${side?'B':'A'}`;scene.add(group);
      const canvas=document.createElement('canvas');canvas.width=W;canvas.height=H;
      const ctx=canvas.getContext('2d'),texture=new THREE.CanvasTexture(canvas);texture.colorSpace=THREE.SRGBColorSpace;
      texture.anisotropy=Math.min(8,renderer.capabilities.getMaxAnisotropy());texture.generateMipmaps=false;texture.minFilter=THREE.LinearFilter;
      const surface=new THREE.Mesh(new THREE.PlaneGeometry(BOARD_W,BOARD_H),new THREE.MeshStandardMaterial({map:texture,roughness:.98}));
      group.add(surface);
      for(const y of [-BOARD_H/2,BOARD_H/2])part(group,[0,y,.025],[BOARD_W+.1,.07,.11],frameMaterial);
      for(const px of [-BOARD_W/2,BOARD_W/2])part(group,[px,0,.025],[.07,BOARD_H,.11],frameMaterial);
      part(group,[0,-BOARD_H/2-.07,.06],[.55,.05,.09],metal);
      boards.push({group,canvas,ctx,texture,last:''});
    }
    part(scene,[x,.33,-10.2],[5.4,.07,.23],frameMaterial);
    for(let j=0;j<4;j++)part(scene,[x-1+j*.15,.39,-10.15],[.1,.025,.025],new THREE.MeshStandardMaterial({color:j%2?'#e6d4a0':'#ebe8d9',roughness:1}));
  }
  const chalk=new THREE.Mesh(new THREE.CylinderGeometry(.014,.017,.17,8),new THREE.MeshStandardMaterial({color:'#f3edda',roughness:1}));
  chalk.rotation.z=-.7;chalk.name='Writing chalk';scene.add(chalk);
  const eraser=new THREE.Mesh(new THREE.BoxGeometry(.48,.18,.1),frameMaterial);eraser.name='Moving blackboard eraser';scene.add(eraser);
  const grain=document.createElement('canvas');grain.width=W;grain.height=H;
  const g=grain.getContext('2d');g.fillStyle='#193d33';g.fillRect(0,0,W,H);
  let seed=831;const random=()=>{seed=(seed*1664525+1013904223)>>>0;return seed/4294967296;};
  for(let i=0;i<12000;i++){g.fillStyle=i%2?'#e7f0d808':'#041c1b18';g.fillRect(random()*W,random()*H,1+random()*2,1);}
  const dust=document.createElement('canvas');dust.width=W;dust.height=H;
  const d=dust.getContext('2d');d.fillStyle='#193d3370';
  for(let i=0;i<16000;i++)d.fillRect(random()*W,random()*H,.5+random()*1.5,.7);
  function draw(index){
    const board=boards[index],slot=clock.slots[index],ctx=board.ctx;
    const erasing=index===clock.active&&clock.phase==='erase';
    const key=`${slot.page}:${slot.progress.toFixed(3)}:${erasing?clock.progress.toFixed(3):''}:${version}`;
    if(board.last===key)return;board.last=key;
    ctx.drawImage(grain,0,0);const image=cache.get(slot.page);
    if(image){
      const rows=pages[slot.page].rows;
      // Reveal each complete mathematical row left to right, preserving exact
      // SVG fractions/superscripts. The grain is deterministic, never flickering.
      rows.forEach(([x,y,w,h],row)=>{
        const p=Math.max(0,Math.min(1,slot.progress*rows.length-row));
        if(p>0){ctx.save();ctx.beginPath();ctx.rect(x,y,w*p,h);ctx.clip();ctx.drawImage(image,0,0);ctx.restore();}
      });
      ctx.drawImage(image,0,580,W,60,0,580,W,60);ctx.drawImage(dust,0,0);
      if(erasing){
        const strips=10,step=clock.progress*strips,full=Math.floor(step),partial=step-full;
        for(let row=0;row<=Math.min(full,strips-1);row++){
          const fraction=row<full?1:partial,w=W*fraction,x=row%2?W-w:0,y=row*H/strips;
          if(w>0)ctx.drawImage(grain,x,y,w,H/strips,x,y,w,H/strips);
        }
      }
    }
    board.texture.needsUpdate=true;
  }
  function positionTool(tool,x,y){
    const board=boards[clock.active].group;
    tool.position.set(board.position.x+(x/W-.5)*BOARD_W,board.position.y+(.5-y/H)*BOARD_H,board.position.z+.14);
  }
  function select(page){clock.select(page);targets[Math.floor(clock.active/2)]=clock.active%2;version++;load(clock.page).catch(error=>{loadingError=error;});}
  function update(dt,reduced=false){
    const ready=cache.has(clock.page)&&(clock.slots[clock.active].page<0||cache.has(clock.slots[clock.active].page));
    if(!ready&&!loadingError){load(clock.page).catch(error=>{loadingError=error;});load(clock.slots[clock.active].page).catch(error=>{loadingError=error;});}
    if(playing&&ready&&!loadingError&&!reduced){
      const prior=clock.page;clock.update(dt);
      if(prior!==clock.page){targets[Math.floor(clock.active/2)]=clock.active%2;load(clock.page).catch(error=>{loadingError=error;});}
    }
    for(let pair=0;pair<3;pair++){
      mix[pair]=reduced?targets[pair]:THREE.MathUtils.damp(mix[pair],targets[pair],3,dt);
      boardHeights(mix[pair]).forEach((height,side)=>boards[pair*2+side].group.position.y=height);
    }
    chalk.visible=playing&&!reduced&&ready&&clock.phase==='write';eraser.visible=playing&&!reduced&&ready&&clock.phase==='erase';
    if(chalk.visible){
      const rows=pages[clock.page].rows,t=clock.progress*rows.length,i=Math.min(rows.length-1,Math.floor(t)),[x,y,w,h]=rows[i];
      positionTool(chalk,x+w*(t-i),y+h*.58+Math.sin(t*90)*h*.14);
    }
    if(eraser.visible){const t=clock.progress*10,row=Math.min(9,Math.floor(t)),p=t-row;positionTool(eraser,(row%2?1-p:p)*W,(row+.5)*H/10);}
    accumulator+=dt;
    if(accumulator>=.05||version){boards.forEach((_,i)=>draw(i));accumulator=0;version=0;}
  }
  // Reduced-motion users get complete static pages and explicit page controls.
  function staticPage(){clock.startWrite();clock.slots[clock.active].progress=1;clock.phase='hold';clock.elapsed=0;version++;}
  boards.forEach((_,i)=>draw(i));
  return {
    update,pages,clock,
    status:()=>loadingError?loadingError.message:`${clock.page+1} / ${pages.length} · ${phaseNames[clock.phase]} · ${pages[clock.page].title}`,
    get playing(){return playing;},set playing(value){playing=value;},
    select,step(delta){select(clock.page+delta);},rewrite(){select(clock.page);},staticPage,
    lift(pair,value){targets[pair]=THREE.MathUtils.clamp(Number(value),0,1);},
    heights:()=>[...targets],focus:()=>new THREE.Vector3(boards[clock.active].group.position.x,2.6,-10.4),
    dispose(){boards.forEach(board=>{board.texture.dispose();board.group.traverse(object=>{object.geometry?.dispose();object.material?.dispose();});});cache.clear();}
  };
}
