// Scene units are metres. Use fixed region anchors, never the moving camera target.
export function regionAnchor(shot){const points=shot?.hallOrbit?shot.targets:shot?.positions;if(!points?.length)return null;return points.reduce((sum,p)=>sum.map((v,i)=>v+p[i]/points.length),[0,0,0]);}
export function distanceLabel(position,anchor){if(!anchor)return '';const metres=Math.hypot(...anchor.map((v,i)=>position[i]-v));return metres<1000?Math.round(metres)+' m':(metres/1000).toFixed(1)+' km';}
