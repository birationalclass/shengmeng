// One geometry contract for the SVG, KaTeX plane and spectral-page projection.
// Crop unused view-box space at the viewport; never squeeze an individual layer.
export const DIAGRAM_VIEWBOX=Object.freeze({width:840,height:525});
export function fitDiagramSurface(viewport,surface,scaleProperty){
 const {width,height}=DIAGRAM_VIEWBOX,bounds=viewport.getBoundingClientRect();
 const contentHeight=Number(getComputedStyle(viewport).getPropertyValue('--diagram-content-height'))||height;
 const scale=Math.max(0,Math.min(bounds.width/width,bounds.height/contentHeight));
 surface.style.width=`${width*scale}px`;
 surface.style.height=`${height*scale}px`;
 surface.style.setProperty(scaleProperty,String(scale));
 return scale;
}
