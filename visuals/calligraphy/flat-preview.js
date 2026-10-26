import {prepareVolume} from './engine/surface.js?v=21';
import {sampleRailSection} from './engine/yang-volume.js';
import {sampleSection} from './engine/stroke-volume.js';
import {flatHomepagePaths} from './homepage-font.js?v=21';

// Project the selected authored geometry into XY, with no camera, lighting or
// perspective. This is the same letter layout, never an unrelated system font.
export function flatGlyph(glyph){
 if(glyph.homepage)return flatHomepagePaths(glyph);
 const paths=[];let minX=Infinity,minY=Infinity,maxX=-Infinity,maxY=-Infinity;
 const point=p=>{const x=p.x,y=-p.y;minX=Math.min(minX,x);maxX=Math.max(maxX,x);minY=Math.min(minY,y);maxY=Math.max(maxY,y);return [x,y];};
 for(const stroke of glyph.strokes||[]){
  const kind=stroke.kind||glyph.kind,spec=prepareVolume(stroke,kind,1,0),a=[],b=[];
  for(let i=0;i<=400;i++){
   if(kind==='centerline'){const q=sampleSection(spec,i/400);a.push(point(q.center.clone().addScaledVector(q.n,-q.width)));b.push(point(q.center.clone().addScaledVector(q.n,q.width)));}
   else{const q=sampleRailSection(spec,i/400);a.push(point(q.a));b.push(point(q.b));}
  }
  paths.push([...a,...b.reverse()].map((p,i)=>(i?'L':'M')+p.map(v=>v.toFixed(4)).join(',')).join(' ')+'Z');
 }
 if(!paths.length)return {paths:[],viewBox:[0,0,1,1]};
 const pad=Math.max(maxX-minX,maxY-minY)*.07;
 return {paths,viewBox:[minX-pad,minY-pad,maxX-minX+2*pad,maxY-minY+2*pad]};
}
export function updateFlatPreview(glyph){
 const area=document.getElementById('flat-preview'),svg=document.getElementById('flat-image'),hasGlyph=!!glyph.text;
 document.body.classList.toggle('has-glyph',hasGlyph);document.body.classList.toggle('homepage-layout',hasGlyph&&glyph.layout==='homepage');area.hidden=!hasGlyph;svg.replaceChildren();
 if(!hasGlyph)return;
 const flat=flatGlyph(glyph),ns='http://www.w3.org/2000/svg';svg.setAttribute('viewBox',flat.viewBox.join(' '));svg.setAttribute('aria-label',glyph.text+' · 平面字样');
 for(const entry of flat.paths){const path=document.createElementNS(ns,'path');path.setAttribute('d',typeof entry==='string'?entry:entry.d);if(typeof entry!=='string'){path.setAttribute('transform',entry.transform);path.setAttribute('stroke','currentColor');path.setAttribute('stroke-width',entry.stroke);path.setAttribute('stroke-linejoin','round');path.setAttribute('stroke-linecap','round');}svg.append(path);}
 document.getElementById('flat-style').textContent=glyph.homepage?'主页行书':glyph.modeling?.kouzan?'衡山行书':glyph.modeling?.running?'行草':glyph.modeling?.cursive?'草书':'原有字形';
}
