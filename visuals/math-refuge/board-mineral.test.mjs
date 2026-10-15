import test from 'node:test';import assert from 'node:assert/strict';
import * as T from '../3d/vendor/three.module.js';
import {mineralPixels,setTrackScheme} from './board-mineral.js';
import {createBoardTrayHardware} from './board-tray.js';
import {createBoardHardware} from './board-hardware.js';
import {BOARD_LAYOUT,boardHeights} from './lecture-state.js';
import {updateTextSheen} from './smart-screen.js';
test('black stone stays dark and low contrast, quartz contains mineral depth, and maps are reused',()=>{
 const p=mineralPixels();assert.equal(p,mineralPixels());let min=255,max=0,qmin=255,qmax=0;for(let i=0;i<p.marble.length;i+=4){min=Math.min(min,p.marble[i]);max=Math.max(max,p.marble[i]);qmin=Math.min(qmin,p.quartz[i]);qmax=Math.max(qmax,p.quartz[i]);assert.equal(p.marble[i+3],255);}assert(min>=20&&max<55);assert(max-min>10);assert(qmin>175&&qmax-qmin>35);
});
test('crystal scheme unifies six independent rims, tray surface and parked eraser without a black strip',()=>{
 const h=createBoardTrayHardware(T),felt=createBoardHardware(T),scene=new T.Scene(),tray=h.create(scene,22.4,0),eraser=h.createEraser(.32,.18,felt),parked=h.createParkedEraser(eraser,0);scene.add(parked);const frames=[];
 for(let pair=0;pair<3;pair++)for(let side=0;side<2;side++){const b=new T.Group();b.position.set(22.4+pair*5.6,boardHeights(0)[side],side*.16);scene.add(b);frames.push(h.createFrame(b,BOARD_LAYOUT.width,BOARD_LAYOUT.height));}
 try{h.setTone('crystal-black');const quartz=tray.children[0].material;assert.equal(quartz,h.crystalMaterial);assert.equal(tray.children[1].material,quartz);assert.equal(eraser.material,quartz);assert.equal(parked.material,quartz);assert.notEqual(parked.children[0].material,quartz);assert(quartz.transmission>0,'optical shell transmits the separate mineral core');assert(quartz.clearcoat>.5);assert(h.crystalCoreMaterial.map.isDataTexture);assert(tray.children[0].children.some(m=>m.name==='Internal quartz mineral inclusion layer'));for(const f of frames)for(const rail of f.children)assert.equal(rail.material,quartz);
 scene.updateMatrixWorld(true);for(let pair=0;pair<3;pair++){const a=new T.Box3().setFromObject(frames[pair*2]),b=new T.Box3().setFromObject(frames[pair*2+1]);assert(b.min.y-a.max.y>.01,'each board has its own rim with visible gap');assert(a.max.x-a.min.x<5.37);}
 const map=h.crystalCoreMaterial.map;h.setTone('pale');assert.notEqual(tray.children[0].material,quartz);assert.notEqual(tray.children[1].material,quartz);h.setTone('crystal-black');assert.equal(h.crystalCoreMaterial.map,map);assert.equal(parked.material,quartz);
 }finally{h.dispose();felt.dispose();}
});
test('modeled crystal rack replaces original channels and clears independent boards through the complete lift travel',()=>{
 const h=createBoardTrayHardware(T),root=new T.Group(),old=new T.MeshStandardMaterial(),m=new T.Mesh(new T.BoxGeometry(1,1,1),old);m.position.set(2.745,2.8,-.1);m.scale.set(.075,4.6,.015);root.add(m);const rack=h.createRack(root,0,BOARD_LAYOUT),boards=[];for(let side=0;side<2;side++){const b=new T.Group();b.position.z=-10.45+side*.16;root.add(b);const frame=h.createFrame(b,BOARD_LAYOUT.width,BOARD_LAYOUT.height);boards.push({b,frame});}const ownBoards=boards.map(v=>v.b);ownBoards.forEach(b=>root.remove(b));
 try{h.setTone('crystal-black');setTrackScheme(root,h.crystalMaterial,true);assert.equal(m.visible,false);assert.equal(rack.visible,true);assert.equal(rack.children.filter(m=>m.name==='Slim beveled quartz guide post').length,2);const posts=rack.children.filter(m=>m.name==='Slim beveled quartz guide post');for(const post of posts){const uv=post.geometry.getAttribute('uv');let low=Infinity,high=-Infinity;for(let i=0;i<uv.count;i++){low=Math.min(low,uv.getY(i));high=Math.max(high,uv.getY(i));}assert(high-low>2,'long posts repeat mineral detail at physical scale instead of stretching one texture');}root.updateMatrixWorld(true);for(let i=0;i<=100;i++)for(let side=0;side<2;side++){const {b,frame}=boards[side];b.position.y=boardHeights(i/100)[side];b.updateMatrixWorld(true);const box=new T.Box3().setFromObject(frame);for(const post of posts)assert(!box.intersectsBox(new T.Box3().setFromObject(post)),'lift rim must not overlap the support post');}setTrackScheme(root,h.crystalMaterial,false);assert.equal(m.visible,true);assert.equal(rack.visible,false);assert.equal(m.scale.x,.075);assert.equal(m.material,old);}finally{h.dispose();old.dispose();m.geometry.dispose();}
});
test('dark control symbols remain dark during hover and press while hit geometry stays unchanged',()=>{
 const m=new T.Mesh(new T.PlaneGeometry(1,1),new T.MeshBasicMaterial());m.userData={smartGlass:true,trayControl:true,trayDarkInk:true,action:'voice:toggle',hovered:true};const scale=m.scale.clone();for(let i=0;i<40;i++)updateTextSheen(T,m,.1,false);assert(m.material.color.r<.1);assert(m.material.color.g<.25);m.userData.pressed=true;updateTextSheen(T,m,.1,false);assert(m.scale.equals(scale));m.material.dispose();m.geometry.dispose();
});
