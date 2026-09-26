import {createVideoLibrary,VIDEO_LIBRARY_URL,videoId,screenPlayerURL} from './video-library.js?v121';
// Project a DOM browser surface onto the four corners of the physical glass.
export function screenTransform(p,width,height){
 if(p.some(v=>v.some(n=>!Number.isFinite(n))))return null;
 const [[x0,y0],[x1,y1],[x2,y2],[x3,y3]]=p;
 const dx1=x1-x2,dx2=x3-x2,dx3=x0-x1+x2-x3,dy1=y1-y2,dy2=y3-y2,dy3=y0-y1+y2-y3;
 const den=dx1*dy2-dx2*dy1;if(Math.abs(den)<1e-5)return null;
 const g=(dx3*dy2-dx2*dy3)/den,h=(dx1*dy3-dx3*dy1)/den;
 // All corners must remain on the same side of the projective pole.
 if(Math.min(1+g,1+h,1+g+h)<=.0001)return null;
 return [(x1-x0+g*x1)/width,(y1-y0+g*y1)/width,0,g/width,(x3-x0+h*x3)/height,(y3-y0+h*y3)/height,0,h/height,0,0,1,0,x0,y0,0,1];
}
export function screenAddress(text){
 const url=new URL(/^https?:\/\//i.test(text)?text:'https://'+text);
 if(!['http:','https:'].includes(url.protocol)||url.username||url.password)throw new Error('请输入网页地址');return url.href;
}
export function createScreenWebview(T){
 const shell=document.createElement('section');shell.className='screen-webview';shell.hidden=true;shell.setAttribute('aria-label','智慧屏网页');
 shell.innerHTML='<header><button type="button" data-nav="back" aria-label="返回上一个地址">←</button><button type="button" data-nav="forward" aria-label="前进到下一个地址">→</button><button type="button" data-nav="reload" aria-label="刷新网页">↻</button><button type="button" data-nav="home" aria-label="影视主页">⌂</button><form><input aria-label="智慧屏浏览器地址" placeholder="输入网址" autocomplete="off" spellcheck="false"><button type="submit" aria-label="访问网址">↵</button></form><button type="button" data-nav="videos" aria-label="视频列表" title="视频列表">▤</button><button type="button" data-nav="fit" aria-label="屏内全屏" title="屏内全屏">⛶</button><button type="button" data-nav="close" aria-label="关闭屏内浏览器">×</button></header><iframe title="智慧屏影视网页" sandbox="allow-scripts allow-same-origin allow-forms allow-presentation" allow="fullscreen &#39;none&#39;; picture-in-picture &#39;none&#39;; encrypted-media; autoplay" referrerpolicy="strict-origin-when-cross-origin"></iframe><div class="embed-blocked" hidden></div><button type="button" class="screen-fit-exit" data-nav="exit-fit" aria-label="退出屏内全屏" title="退出屏内全屏" hidden>×</button>';
 // Punch a depth-tested transparent window in the WebGL canvas. The DOM page
 // lives underneath; nearer seats/walls keep their colour and depth normally.
 const portal=new T.Mesh(new T.PlaneGeometry(16,6.58),new T.MeshBasicMaterial({color:0x000000,opacity:0,transparent:false,blending:T.NoBlending,depthTest:true,depthWrite:true,toneMapped:false}));
 portal.name='Smart browser depth portal';portal.position.set(28,1.91,-11.27);portal.renderOrder=9999;portal.visible=false;
 const canvas=document.getElementById('world'),raycast=new T.Raycaster(),pointer=new T.Vector2();let activeCamera=null,activeScene=null;
 const visible=o=>{for(let p=o;p;p=p.parent)if(!p.visible)return false;return true;};
 function routePointer(e){
  if(!canvas||shell.hidden||!activeCamera||!activeScene){if(canvas)canvas.style.pointerEvents='';return;}
  const box=shell.getBoundingClientRect();if(e.clientX<box.left||e.clientX>box.right||e.clientY<box.top||e.clientY>box.bottom){canvas.style.pointerEvents='';return;}
  pointer.set(e.clientX/innerWidth*2-1,1-e.clientY/innerHeight*2);raycast.setFromCamera(pointer,activeCamera);
  const hit=raycast.intersectObject(portal,false)[0];if(!hit){canvas.style.pointerEvents='';return;}
  raycast.far=hit.distance-.005;
  const blocked=raycast.intersectObjects(activeScene.children,true).some(h=>h.object!==portal&&visible(h.object)&&(()=>{const m=Array.isArray(h.object.material)?h.object.material[h.face?.materialIndex||0]:h.object.material;return m&&m.visible&&m.depthWrite&&m.opacity>.95&&!m.transparent;})());
  raycast.far=Infinity;canvas.style.pointerEvents=blocked?'':'none';
 }
 document.addEventListener('pointermove',routePointer,true);
 document.body.append(shell);const frame=shell.querySelector('iframe'),address=shell.querySelector('input'),blocked=shell.querySelector('.embed-blocked');let site=null,history=[],index=-1,fit=false,homeURL='https://www.bilibili.com/';
 const library=createVideoLibrary(navigate);shell.append(library.root);const fitButton=shell.querySelector('[data-nav=fit]'),fitExit=shell.querySelector('[data-nav=exit-fit]');
 function setFit(value){fit=value;fitExit.hidden=!fit;if(fit)library.hide();shell.classList.toggle('screen-player-fit',fit);fitButton.setAttribute('aria-label',fit?'退出屏内全屏':'屏内全屏');fitButton.title=fit?'退出屏内全屏':'屏内全屏';}
 const back=shell.querySelector('[data-nav="back"]'),forward=shell.querySelector('[data-nav="forward"]');
 function load(url){setFit(false);library.hide();address.value=url===VIDEO_LIBRARY_URL?'视频列表':url;back.disabled=index<=0;forward.disabled=index>=history.length-1;
  fitButton.disabled=!videoId(url);
  if(url===VIDEO_LIBRARY_URL){frame.hidden=true;frame.src='about:blank';blocked.hidden=true;library.show();return;}
  const id=videoId(url);if(id)library.remember(id);
  const restricted=new URL(url).hostname==='v.qq.com';blocked.hidden=!restricted;frame.hidden=restricted;
  blocked.textContent=restricted?'腾讯视频不允许此网站嵌入其主页。请在地址栏选择允许嵌入的网页。':'';
  frame.src=restricted?'about:blank':url;
 }
 function navigate(url){try{url=url===VIDEO_LIBRARY_URL?url:screenAddress(url);history=history.slice(0,index+1);history.push(url);index++;site={url};load(url);}catch{address.setCustomValidity('请输入有效的 HTTP 或 HTTPS 网页地址');address.reportValidity();}}
 function close(){library.hide();setFit(false);site=null;shell.hidden=true;portal.visible=false;if(canvas)canvas.style.pointerEvents='';frame.src='about:blank';}
 shell.querySelector('form').addEventListener('submit',e=>{e.preventDefault();navigate(address.value);});address.addEventListener('input',()=>address.setCustomValidity(''));
 for(const button of shell.querySelectorAll('[data-nav]'))button.addEventListener('click',()=>{const action=button.dataset.nav;if(action==='close'){close();return;}if(action==='home'){navigate(homeURL);return;}if(action==='videos'){if(library.root.hidden)library.show();else library.hide();return;}if(action==='exit-fit'){setFit(false);frame.src=history[index];fitButton.focus();return;}if(action==='fit'){const url=history[index],player=screenPlayerURL(url);if(!player)return;setFit(!fit);frame.src=fit?player:url;return;}if(action==='back'&&index>0)index--;if(action==='forward'&&index<history.length-1)index++;if(index>=0)load(history[index]);});
 for(const type of ['pointerdown','pointerup','wheel','keydown'])shell.addEventListener(type,e=>e.stopPropagation());
 const corners=[[20,5.20],[36,5.20],[36,-1.38],[20,-1.38]].map(([x,y])=>new T.Vector3(x,y,-11.27));
 return {get isOpen(){return Boolean(site);},open(value){frame.title=value.label+' · 智慧屏网页';homeURL=value.url;navigate(value.url);},close,
 update(camera,lecture,scene){portal.visible=false;if(!site)return;activeCamera=camera;activeScene=scene;const state=lecture?.screenMode;if(!state?.power||state.mode!=='media'){close();return;}
  if(lecture.storageProgress<.99){shell.hidden=true;return;}
  lecture.root.updateWorldMatrix(true,false);const eye=lecture.root.worldToLocal(camera.position.clone());if(eye.z<=-11.27+.35){shell.hidden=true;return;}
  // At grazing angles a DOM homography becomes ill-conditioned even while
  // the physical mesh is still clipped safely by WebGL. Suppress both together.
  const distance=eye.distanceTo(new T.Vector3(28,1.91,-11.27));
  if((eye.z+11.27)/Math.max(.001,distance)<.075){shell.hidden=true;if(canvas)canvas.style.pointerEvents='';return;}
  const worldCorners=corners.map(v=>v.clone().applyMatrix4(lecture.root.matrixWorld));
  const depths=worldCorners.map(v=>-v.clone().applyMatrix4(camera.matrixWorldInverse).z);
  if(Math.min(...depths)<Math.max(camera.near*3,.25)){shell.hidden=true;if(canvas)canvas.style.pointerEvents='';return;}
  const projected=corners.map(v=>v.clone().applyMatrix4(lecture.root.matrixWorld).project(camera));
  if(projected.some(p=>p.z<=-1||p.z>=1)){shell.hidden=true;return;}
  const matrix=screenTransform(projected.map(p=>[(p.x+1)*innerWidth/2,(1-p.y)*innerHeight/2]),1440,592.2);
  if(!matrix){shell.hidden=true;return;}shell.style.transform='matrix3d('+matrix.join(',')+')';shell.hidden=false;if(portal.parent!==lecture.root)lecture.root.add(portal);portal.visible=true;
 },dispose(){close();document.removeEventListener('pointermove',routePointer,true);portal.removeFromParent();portal.geometry.dispose();portal.material.dispose();shell.remove();}};
}
