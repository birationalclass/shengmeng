import {seaDepthAt} from './sea-depth.js?v100-reef';
import {BUILDING_SCALE as S} from './site-layout.js';
export const OCEAN_ORIGIN=[88,-.65*S,-35];
export function studyCoordinates(x,z){return [88-x,z+35];}
export function findShore(z){let left=54,right=84;if(seaDepthAt(left,z)>=0)return null;for(let i=0;i<28;i++){const mid=(left+right)/2;if(seaDepthAt(mid,z)>0)right=mid;else left=mid;}return (left+right)*.5;}
export function shoreDistance(position){let distance=Infinity;for(let z=-24;z<=43;z+=1){const x=findShore(z);if(x!==null)distance=Math.min(distance,Math.hypot(position.x-x*S,position.z-z*S,position.y-OCEAN_ORIGIN[1]));}return distance;}
export function surfGain(distance){return .32/(1+(Math.max(0,distance)/24)**1.65);}
