import*as Y from"../3d/vendor/three.module.js";import{Controls as Qo,MOUSE as Me,Quaternion as qt,Spherical as Xt,TOUCH as xe,Vector2 as ee,Vector3 as se,Plane as $o,Ray as Jo,MathUtils as ea}from"../3d/vendor/three.module.js";var Yt={type:"change"},ut={type:"start"},Kt={type:"end"},Ge=new Jo,Zt=new $o,ta=Math.cos(70*ea.DEG2RAD),F=new se,Q=2*Math.PI,H={NONE:-1,ROTATE:0,DOLLY:1,PAN:2,TOUCH_ROTATE:3,TOUCH_PAN:4,TOUCH_DOLLY_PAN:5,TOUCH_DOLLY_ROTATE:6},ct=1e-6,Ne=class extends Qo{constructor(e,o=null){super(e,o),this.state=H.NONE,this.target=new se,this.cursor=new se,this.minDistance=0,this.maxDistance=1/0,this.minZoom=0,this.maxZoom=1/0,this.minTargetRadius=0,this.maxTargetRadius=1/0,this.minPolarAngle=0,this.maxPolarAngle=Math.PI,this.minAzimuthAngle=-1/0,this.maxAzimuthAngle=1/0,this.enableDamping=!1,this.dampingFactor=.05,this.enableZoom=!0,this.zoomSpeed=1,this.enableRotate=!0,this.rotateSpeed=1,this.keyRotateSpeed=1,this.enablePan=!0,this.panSpeed=1,this.screenSpacePanning=!0,this.keyPanSpeed=7,this.zoomToCursor=!1,this.autoRotate=!1,this.autoRotateSpeed=2,this.keys={LEFT:"ArrowLeft",UP:"ArrowUp",RIGHT:"ArrowRight",BOTTOM:"ArrowDown"},this.mouseButtons={LEFT:Me.ROTATE,MIDDLE:Me.DOLLY,RIGHT:Me.PAN},this.touches={ONE:xe.ROTATE,TWO:xe.DOLLY_PAN},this.target0=this.target.clone(),this.position0=this.object.position.clone(),this.zoom0=this.object.zoom,this._domElementKeyEvents=null,this._lastPosition=new se,this._lastQuaternion=new qt,this._lastTargetPosition=new se,this._quat=new qt().setFromUnitVectors(e.up,new se(0,1,0)),this._quatInverse=this._quat.clone().invert(),this._spherical=new Xt,this._sphericalDelta=new Xt,this._scale=1,this._panOffset=new se,this._rotateStart=new ee,this._rotateEnd=new ee,this._rotateDelta=new ee,this._panStart=new ee,this._panEnd=new ee,this._panDelta=new ee,this._dollyStart=new ee,this._dollyEnd=new ee,this._dollyDelta=new ee,this._dollyDirection=new se,this._mouse=new ee,this._performCursorZoom=!1,this._pointers=[],this._pointerPositions={},this._controlActive=!1,this._onPointerMove=aa.bind(this),this._onPointerDown=oa.bind(this),this._onPointerUp=sa.bind(this),this._onContextMenu=ha.bind(this),this._onMouseWheel=ia.bind(this),this._onKeyDown=la.bind(this),this._onTouchStart=ca.bind(this),this._onTouchMove=ua.bind(this),this._onMouseDown=ra.bind(this),this._onMouseMove=na.bind(this),this._interceptControlDown=da.bind(this),this._interceptControlUp=fa.bind(this),this.domElement!==null&&this.connect(this.domElement),this.update()}connect(e){super.connect(e),this.domElement.addEventListener("pointerdown",this._onPointerDown),this.domElement.addEventListener("pointercancel",this._onPointerUp),this.domElement.addEventListener("contextmenu",this._onContextMenu),this.domElement.addEventListener("wheel",this._onMouseWheel,{passive:!1}),this.domElement.getRootNode().addEventListener("keydown",this._interceptControlDown,{passive:!0,capture:!0}),this.domElement.style.touchAction="none"}disconnect(){this.domElement.removeEventListener("pointerdown",this._onPointerDown),this.domElement.removeEventListener("pointermove",this._onPointerMove),this.domElement.removeEventListener("pointerup",this._onPointerUp),this.domElement.removeEventListener("pointercancel",this._onPointerUp),this.domElement.removeEventListener("wheel",this._onMouseWheel),this.domElement.removeEventListener("contextmenu",this._onContextMenu),this.stopListenToKeyEvents(),this.domElement.getRootNode().removeEventListener("keydown",this._interceptControlDown,{capture:!0}),this.domElement.style.touchAction="auto"}dispose(){this.disconnect()}getPolarAngle(){return this._spherical.phi}getAzimuthalAngle(){return this._spherical.theta}getDistance(){return this.object.position.distanceTo(this.target)}listenToKeyEvents(e){e.addEventListener("keydown",this._onKeyDown),this._domElementKeyEvents=e}stopListenToKeyEvents(){this._domElementKeyEvents!==null&&(this._domElementKeyEvents.removeEventListener("keydown",this._onKeyDown),this._domElementKeyEvents=null)}saveState(){this.target0.copy(this.target),this.position0.copy(this.object.position),this.zoom0=this.object.zoom}reset(){this.target.copy(this.target0),this.object.position.copy(this.position0),this.object.zoom=this.zoom0,this.object.updateProjectionMatrix(),this.dispatchEvent(Yt),this.update(),this.state=H.NONE}update(e=null){let o=this.object.position;F.copy(o).sub(this.target),F.applyQuaternion(this._quat),this._spherical.setFromVector3(F),this.autoRotate&&this.state===H.NONE&&this._rotateLeft(this._getAutoRotationAngle(e)),this.enableDamping?(this._spherical.theta+=this._sphericalDelta.theta*this.dampingFactor,this._spherical.phi+=this._sphericalDelta.phi*this.dampingFactor):(this._spherical.theta+=this._sphericalDelta.theta,this._spherical.phi+=this._sphericalDelta.phi);let a=this.minAzimuthAngle,s=this.maxAzimuthAngle;isFinite(a)&&isFinite(s)&&(a<-Math.PI?a+=Q:a>Math.PI&&(a-=Q),s<-Math.PI?s+=Q:s>Math.PI&&(s-=Q),a<=s?this._spherical.theta=Math.max(a,Math.min(s,this._spherical.theta)):this._spherical.theta=this._spherical.theta>(a+s)/2?Math.max(a,this._spherical.theta):Math.min(s,this._spherical.theta)),this._spherical.phi=Math.max(this.minPolarAngle,Math.min(this.maxPolarAngle,this._spherical.phi)),this._spherical.makeSafe(),this.enableDamping===!0?this.target.addScaledVector(this._panOffset,this.dampingFactor):this.target.add(this._panOffset),this.target.sub(this.cursor),this.target.clampLength(this.minTargetRadius,this.maxTargetRadius),this.target.add(this.cursor);let n=!1;if(this.zoomToCursor&&this._performCursorZoom||this.object.isOrthographicCamera)this._spherical.radius=this._clampDistance(this._spherical.radius);else{let i=this._spherical.radius;this._spherical.radius=this._clampDistance(this._spherical.radius*this._scale),n=i!=this._spherical.radius}if(F.setFromSpherical(this._spherical),F.applyQuaternion(this._quatInverse),o.copy(this.target).add(F),this.object.lookAt(this.target),this.enableDamping===!0?(this._sphericalDelta.theta*=1-this.dampingFactor,this._sphericalDelta.phi*=1-this.dampingFactor,this._panOffset.multiplyScalar(1-this.dampingFactor)):(this._sphericalDelta.set(0,0,0),this._panOffset.set(0,0,0)),this.zoomToCursor&&this._performCursorZoom){let i=null;if(this.object.isPerspectiveCamera){let l=F.length();i=this._clampDistance(l*this._scale);let r=l-i;this.object.position.addScaledVector(this._dollyDirection,r),this.object.updateMatrixWorld(),n=!!r}else if(this.object.isOrthographicCamera){let l=new se(this._mouse.x,this._mouse.y,0);l.unproject(this.object);let r=this.object.zoom;this.object.zoom=Math.max(this.minZoom,Math.min(this.maxZoom,this.object.zoom/this._scale)),this.object.updateProjectionMatrix(),n=r!==this.object.zoom;let p=new se(this._mouse.x,this._mouse.y,0);p.unproject(this.object),this.object.position.sub(p).add(l),this.object.updateMatrixWorld(),i=F.length()}else console.warn("WARNING: OrbitControls.js encountered an unknown camera type - zoom to cursor disabled."),this.zoomToCursor=!1;i!==null&&(this.screenSpacePanning?this.target.set(0,0,-1).transformDirection(this.object.matrix).multiplyScalar(i).add(this.object.position):(Ge.origin.copy(this.object.position),Ge.direction.set(0,0,-1).transformDirection(this.object.matrix),Math.abs(this.object.up.dot(Ge.direction))<ta?this.object.lookAt(this.target):(Zt.setFromNormalAndCoplanarPoint(this.object.up,this.target),Ge.intersectPlane(Zt,this.target))))}else if(this.object.isOrthographicCamera){let i=this.object.zoom;this.object.zoom=Math.max(this.minZoom,Math.min(this.maxZoom,this.object.zoom/this._scale)),i!==this.object.zoom&&(this.object.updateProjectionMatrix(),n=!0)}return this._scale=1,this._performCursorZoom=!1,n||this._lastPosition.distanceToSquared(this.object.position)>ct||8*(1-this._lastQuaternion.dot(this.object.quaternion))>ct||this._lastTargetPosition.distanceToSquared(this.target)>ct?(this.dispatchEvent(Yt),this._lastPosition.copy(this.object.position),this._lastQuaternion.copy(this.object.quaternion),this._lastTargetPosition.copy(this.target),!0):!1}_getAutoRotationAngle(e){return e!==null?Q/60*this.autoRotateSpeed*e:Q/60/60*this.autoRotateSpeed}_getZoomScale(e){let o=Math.abs(e*.01);return Math.pow(.95,this.zoomSpeed*o)}_rotateLeft(e){this._sphericalDelta.theta-=e}_rotateUp(e){this._sphericalDelta.phi-=e}_panLeft(e,o){F.setFromMatrixColumn(o,0),F.multiplyScalar(-e),this._panOffset.add(F)}_panUp(e,o){this.screenSpacePanning===!0?F.setFromMatrixColumn(o,1):(F.setFromMatrixColumn(o,0),F.crossVectors(this.object.up,F)),F.multiplyScalar(e),this._panOffset.add(F)}_pan(e,o){let a=this.domElement;if(this.object.isPerspectiveCamera){let s=this.object.position;F.copy(s).sub(this.target);let n=F.length();n*=Math.tan(this.object.fov/2*Math.PI/180),this._panLeft(2*e*n/a.clientHeight,this.object.matrix),this._panUp(2*o*n/a.clientHeight,this.object.matrix)}else this.object.isOrthographicCamera?(this._panLeft(e*(this.object.right-this.object.left)/this.object.zoom/a.clientWidth,this.object.matrix),this._panUp(o*(this.object.top-this.object.bottom)/this.object.zoom/a.clientHeight,this.object.matrix)):(console.warn("WARNING: OrbitControls.js encountered an unknown camera type - pan disabled."),this.enablePan=!1)}_dollyOut(e){this.object.isPerspectiveCamera||this.object.isOrthographicCamera?this._scale/=e:(console.warn("WARNING: OrbitControls.js encountered an unknown camera type - dolly/zoom disabled."),this.enableZoom=!1)}_dollyIn(e){this.object.isPerspectiveCamera||this.object.isOrthographicCamera?this._scale*=e:(console.warn("WARNING: OrbitControls.js encountered an unknown camera type - dolly/zoom disabled."),this.enableZoom=!1)}_updateZoomParameters(e,o){if(!this.zoomToCursor)return;this._performCursorZoom=!0;let a=this.domElement.getBoundingClientRect(),s=e-a.left,n=o-a.top,i=a.width,l=a.height;this._mouse.x=s/i*2-1,this._mouse.y=-(n/l)*2+1,this._dollyDirection.set(this._mouse.x,this._mouse.y,1).unproject(this.object).sub(this.object.position).normalize()}_clampDistance(e){return Math.max(this.minDistance,Math.min(this.maxDistance,e))}_handleMouseDownRotate(e){this._rotateStart.set(e.clientX,e.clientY)}_handleMouseDownDolly(e){this._updateZoomParameters(e.clientX,e.clientX),this._dollyStart.set(e.clientX,e.clientY)}_handleMouseDownPan(e){this._panStart.set(e.clientX,e.clientY)}_handleMouseMoveRotate(e){this._rotateEnd.set(e.clientX,e.clientY),this._rotateDelta.subVectors(this._rotateEnd,this._rotateStart).multiplyScalar(this.rotateSpeed);let o=this.domElement;this._rotateLeft(Q*this._rotateDelta.x/o.clientHeight),this._rotateUp(Q*this._rotateDelta.y/o.clientHeight),this._rotateStart.copy(this._rotateEnd),this.update()}_handleMouseMoveDolly(e){this._dollyEnd.set(e.clientX,e.clientY),this._dollyDelta.subVectors(this._dollyEnd,this._dollyStart),this._dollyDelta.y>0?this._dollyOut(this._getZoomScale(this._dollyDelta.y)):this._dollyDelta.y<0&&this._dollyIn(this._getZoomScale(this._dollyDelta.y)),this._dollyStart.copy(this._dollyEnd),this.update()}_handleMouseMovePan(e){this._panEnd.set(e.clientX,e.clientY),this._panDelta.subVectors(this._panEnd,this._panStart).multiplyScalar(this.panSpeed),this._pan(this._panDelta.x,this._panDelta.y),this._panStart.copy(this._panEnd),this.update()}_handleMouseWheel(e){this._updateZoomParameters(e.clientX,e.clientY),e.deltaY<0?this._dollyIn(this._getZoomScale(e.deltaY)):e.deltaY>0&&this._dollyOut(this._getZoomScale(e.deltaY)),this.update()}_handleKeyDown(e){let o=!1;switch(e.code){case this.keys.UP:e.ctrlKey||e.metaKey||e.shiftKey?this.enableRotate&&this._rotateUp(Q*this.keyRotateSpeed/this.domElement.clientHeight):this.enablePan&&this._pan(0,this.keyPanSpeed),o=!0;break;case this.keys.BOTTOM:e.ctrlKey||e.metaKey||e.shiftKey?this.enableRotate&&this._rotateUp(-Q*this.keyRotateSpeed/this.domElement.clientHeight):this.enablePan&&this._pan(0,-this.keyPanSpeed),o=!0;break;case this.keys.LEFT:e.ctrlKey||e.metaKey||e.shiftKey?this.enableRotate&&this._rotateLeft(Q*this.keyRotateSpeed/this.domElement.clientHeight):this.enablePan&&this._pan(this.keyPanSpeed,0),o=!0;break;case this.keys.RIGHT:e.ctrlKey||e.metaKey||e.shiftKey?this.enableRotate&&this._rotateLeft(-Q*this.keyRotateSpeed/this.domElement.clientHeight):this.enablePan&&this._pan(-this.keyPanSpeed,0),o=!0;break}o&&(e.preventDefault(),this.update())}_handleTouchStartRotate(e){if(this._pointers.length===1)this._rotateStart.set(e.pageX,e.pageY);else{let o=this._getSecondPointerPosition(e),a=.5*(e.pageX+o.x),s=.5*(e.pageY+o.y);this._rotateStart.set(a,s)}}_handleTouchStartPan(e){if(this._pointers.length===1)this._panStart.set(e.pageX,e.pageY);else{let o=this._getSecondPointerPosition(e),a=.5*(e.pageX+o.x),s=.5*(e.pageY+o.y);this._panStart.set(a,s)}}_handleTouchStartDolly(e){let o=this._getSecondPointerPosition(e),a=e.pageX-o.x,s=e.pageY-o.y,n=Math.sqrt(a*a+s*s);this._dollyStart.set(0,n)}_handleTouchStartDollyPan(e){this.enableZoom&&this._handleTouchStartDolly(e),this.enablePan&&this._handleTouchStartPan(e)}_handleTouchStartDollyRotate(e){this.enableZoom&&this._handleTouchStartDolly(e),this.enableRotate&&this._handleTouchStartRotate(e)}_handleTouchMoveRotate(e){if(this._pointers.length==1)this._rotateEnd.set(e.pageX,e.pageY);else{let a=this._getSecondPointerPosition(e),s=.5*(e.pageX+a.x),n=.5*(e.pageY+a.y);this._rotateEnd.set(s,n)}this._rotateDelta.subVectors(this._rotateEnd,this._rotateStart).multiplyScalar(this.rotateSpeed);let o=this.domElement;this._rotateLeft(Q*this._rotateDelta.x/o.clientHeight),this._rotateUp(Q*this._rotateDelta.y/o.clientHeight),this._rotateStart.copy(this._rotateEnd)}_handleTouchMovePan(e){if(this._pointers.length===1)this._panEnd.set(e.pageX,e.pageY);else{let o=this._getSecondPointerPosition(e),a=.5*(e.pageX+o.x),s=.5*(e.pageY+o.y);this._panEnd.set(a,s)}this._panDelta.subVectors(this._panEnd,this._panStart).multiplyScalar(this.panSpeed),this._pan(this._panDelta.x,this._panDelta.y),this._panStart.copy(this._panEnd)}_handleTouchMoveDolly(e){let o=this._getSecondPointerPosition(e),a=e.pageX-o.x,s=e.pageY-o.y,n=Math.sqrt(a*a+s*s);this._dollyEnd.set(0,n),this._dollyDelta.set(0,Math.pow(this._dollyEnd.y/this._dollyStart.y,this.zoomSpeed)),this._dollyOut(this._dollyDelta.y),this._dollyStart.copy(this._dollyEnd);let i=(e.pageX+o.x)*.5,l=(e.pageY+o.y)*.5;this._updateZoomParameters(i,l)}_handleTouchMoveDollyPan(e){this.enableZoom&&this._handleTouchMoveDolly(e),this.enablePan&&this._handleTouchMovePan(e)}_handleTouchMoveDollyRotate(e){this.enableZoom&&this._handleTouchMoveDolly(e),this.enableRotate&&this._handleTouchMoveRotate(e)}_addPointer(e){this._pointers.push(e.pointerId)}_removePointer(e){delete this._pointerPositions[e.pointerId];for(let o=0;o<this._pointers.length;o++)if(this._pointers[o]==e.pointerId){this._pointers.splice(o,1);return}}_isTrackingPointer(e){for(let o=0;o<this._pointers.length;o++)if(this._pointers[o]==e.pointerId)return!0;return!1}_trackPointer(e){let o=this._pointerPositions[e.pointerId];o===void 0&&(o=new ee,this._pointerPositions[e.pointerId]=o),o.set(e.pageX,e.pageY)}_getSecondPointerPosition(e){let o=e.pointerId===this._pointers[0]?this._pointers[1]:this._pointers[0];return this._pointerPositions[o]}_customWheelEvent(e){let o=e.deltaMode,a={clientX:e.clientX,clientY:e.clientY,deltaY:e.deltaY};switch(o){case 1:a.deltaY*=16;break;case 2:a.deltaY*=100;break}return e.ctrlKey&&!this._controlActive&&(a.deltaY*=10),a}};function oa(t){this.enabled!==!1&&(this._pointers.length===0&&(this.domElement.setPointerCapture(t.pointerId),this.domElement.addEventListener("pointermove",this._onPointerMove),this.domElement.addEventListener("pointerup",this._onPointerUp)),!this._isTrackingPointer(t)&&(this._addPointer(t),t.pointerType==="touch"?this._onTouchStart(t):this._onMouseDown(t)))}function aa(t){this.enabled!==!1&&(t.pointerType==="touch"?this._onTouchMove(t):this._onMouseMove(t))}function sa(t){switch(this._removePointer(t),this._pointers.length){case 0:this.domElement.releasePointerCapture(t.pointerId),this.domElement.removeEventListener("pointermove",this._onPointerMove),this.domElement.removeEventListener("pointerup",this._onPointerUp),this.dispatchEvent(Kt),this.state=H.NONE;break;case 1:let e=this._pointers[0],o=this._pointerPositions[e];this._onTouchStart({pointerId:e,pageX:o.x,pageY:o.y});break}}function ra(t){let e;switch(t.button){case 0:e=this.mouseButtons.LEFT;break;case 1:e=this.mouseButtons.MIDDLE;break;case 2:e=this.mouseButtons.RIGHT;break;default:e=-1}switch(e){case Me.DOLLY:if(this.enableZoom===!1)return;this._handleMouseDownDolly(t),this.state=H.DOLLY;break;case Me.ROTATE:if(t.ctrlKey||t.metaKey||t.shiftKey){if(this.enablePan===!1)return;this._handleMouseDownPan(t),this.state=H.PAN}else{if(this.enableRotate===!1)return;this._handleMouseDownRotate(t),this.state=H.ROTATE}break;case Me.PAN:if(t.ctrlKey||t.metaKey||t.shiftKey){if(this.enableRotate===!1)return;this._handleMouseDownRotate(t),this.state=H.ROTATE}else{if(this.enablePan===!1)return;this._handleMouseDownPan(t),this.state=H.PAN}break;default:this.state=H.NONE}this.state!==H.NONE&&this.dispatchEvent(ut)}function na(t){switch(this.state){case H.ROTATE:if(this.enableRotate===!1)return;this._handleMouseMoveRotate(t);break;case H.DOLLY:if(this.enableZoom===!1)return;this._handleMouseMoveDolly(t);break;case H.PAN:if(this.enablePan===!1)return;this._handleMouseMovePan(t);break}}function ia(t){this.enabled===!1||this.enableZoom===!1||this.state!==H.NONE||(t.preventDefault(),this.dispatchEvent(ut),this._handleMouseWheel(this._customWheelEvent(t)),this.dispatchEvent(Kt))}function la(t){this.enabled!==!1&&this._handleKeyDown(t)}function ca(t){switch(this._trackPointer(t),this._pointers.length){case 1:switch(this.touches.ONE){case xe.ROTATE:if(this.enableRotate===!1)return;this._handleTouchStartRotate(t),this.state=H.TOUCH_ROTATE;break;case xe.PAN:if(this.enablePan===!1)return;this._handleTouchStartPan(t),this.state=H.TOUCH_PAN;break;default:this.state=H.NONE}break;case 2:switch(this.touches.TWO){case xe.DOLLY_PAN:if(this.enableZoom===!1&&this.enablePan===!1)return;this._handleTouchStartDollyPan(t),this.state=H.TOUCH_DOLLY_PAN;break;case xe.DOLLY_ROTATE:if(this.enableZoom===!1&&this.enableRotate===!1)return;this._handleTouchStartDollyRotate(t),this.state=H.TOUCH_DOLLY_ROTATE;break;default:this.state=H.NONE}break;default:this.state=H.NONE}this.state!==H.NONE&&this.dispatchEvent(ut)}function ua(t){switch(this._trackPointer(t),this.state){case H.TOUCH_ROTATE:if(this.enableRotate===!1)return;this._handleTouchMoveRotate(t),this.update();break;case H.TOUCH_PAN:if(this.enablePan===!1)return;this._handleTouchMovePan(t),this.update();break;case H.TOUCH_DOLLY_PAN:if(this.enableZoom===!1&&this.enablePan===!1)return;this._handleTouchMoveDollyPan(t),this.update();break;case H.TOUCH_DOLLY_ROTATE:if(this.enableZoom===!1&&this.enableRotate===!1)return;this._handleTouchMoveDollyRotate(t),this.update();break;default:this.state=H.NONE}}function ha(t){this.enabled!==!1&&t.preventDefault()}function da(t){t.key==="Control"&&(this._controlActive=!0,this.domElement.getRootNode().addEventListener("keyup",this._interceptControlUp,{passive:!0,capture:!0}))}function fa(t){t.key==="Control"&&(this._controlActive=!1,this.domElement.getRootNode().removeEventListener("keyup",this._interceptControlUp,{passive:!0,capture:!0}))}var w=Math.SQRT2,Z=.28,re={west:32.2,east:43.2,north:-11.5,south:11.5,boardX:42.7,clearHeight:4.9};var We=.72;var pe=[[-82,25,-40,1.5],[-77,21,-37,1.7],[-74,3,-34,2.2],[-70,1,-25,1.7],[-65,0,-12,1.4],[-59,-.5,5,1.4],[-47,-1,23,1.6],[-33,-1.9,33,1.7],[-10,-3.04,45,2.2]].map(([t,e,o,a])=>[t-120,e,o,a]),Qt=(t,e,o,a,s)=>.5*(2*e+(-t+o)*s+(2*t-5*e+4*o-a)*s*s+(-t+3*e-3*o+a)*s*s*s);function pa(t){let e=Math.max(0,Math.min(1,t))*(pe.length-1),o=Math.min(pe.length-2,Math.floor(e)),a=e-o,s=pe[Math.max(0,o-1)],n=pe[o],i=pe[o+1],l=pe[Math.min(pe.length-1,o+2)];return{x:Qt(s[0],n[0],i[0],l[0],a),y:n[1]+(i[1]-n[1])*a,z:Qt(s[2],n[2],i[2],l[2],a),width:n[3]+(i[3]-n[3])*a}}var Ue=Array.from({length:157},(t,e)=>pa(e/156)),Ya={minX:Math.min(...Ue.map(t=>t.x-t.width))-5,maxX:Math.max(...Ue.map(t=>t.x+t.width))+5,minZ:Math.min(...Ue.map(t=>t.z-t.width))-5,maxZ:Math.max(...Ue.map(t=>t.z+t.width))+5};var je={left:19.22,right:36.78,back:-11.4,front:-10.25},$t=[re.boardX-(10.4+je.front)*We/w,re.boardX-(10.4+je.back)*We/w,(je.left-28)*We/w,(je.right-28)*We/w];var ce={minX:-4096,minZ:-8192,size:16384},ma=50;function be(t){let e=(1-Math.cos(t))/2;return[e*1e3,-500*Math.sin(t)*Math.sqrt(2-e)]}function Ee(t){let e=2+t*t;return[1e3*e,-1e3*t*Math.sqrt(e*(e-1))]}function ht(t,e,o){let a=Math.max(0,Math.min(1,(o-t)/(e-t)));return a*a*(3-2*a)}function va(t,e){let o=ht(1800,7300,Math.abs(e));return 24*ht(1200,1600,t)*o*o}function ga(t,e,o){return(.07*Math.sin(e*.022+o*.015)+.03*Math.sin(e*.043-o*.027))*(1-ht(40,140,Math.abs(t)))}function De(t,e=0,o=0){return Math.max(-18,.055*(ma-Math.sqrt(t*t+4))+ga(t,e,o)-va(e,o))}function Jt(t){return t.tide+(t.tidal?.28*Math.sin(t.time*Math.PI/20):0)}var dt=`
uniform sampler2D uDistance;
uniform vec2 uOrigin;
uniform float uGrid,uTide;
float curveDistance(vec2 p){
 vec2 uv=(p-vec2(${ce.minX.toFixed(1)},${ce.minZ.toFixed(1)}))/${ce.size.toFixed(1)};
 if(any(lessThan(uv,vec2(0.)))||any(greaterThan(uv,vec2(1.))))return 400.;
 vec2 packed=texture2D(uDistance,uv).rg;
 return dot(packed,vec2(652.8,2.55));
}
float coastalDrop(vec2 p){float descent=smoothstep(1800.,7300.,abs(p.y));return 24.*smoothstep(1200.,1600.,p.x)*descent*descent;}
float sandRelief(float d,vec2 p){return (.07*sin(p.x*.022+p.y*.015)+.03*sin(p.x*.043-p.y*.027))*(1.-smoothstep(40.,140.,abs(d)));}
float beachHeight(vec2 p){float d=curveDistance(p);return max(-18.,.055*(50.-sqrt(d*d+4.))+sandRelief(d,p)-coastalDrop(p));}
vec3 bedNormal(vec2 p){return normalize(vec3(beachHeight(p-vec2(.5,0.))-beachHeight(p+vec2(.5,0.)),1.,beachHeight(p-vec2(0.,.5))-beachHeight(p+vec2(0.,.5))));}
#ifdef COAST_FRAGMENT
vec3 gridColor(vec3 col,vec2 p){
 vec2 q=p/250.;vec2 fw=max(fwidth(q),vec2(.00001));
 vec2 g=abs(fract(q-.5)-.5)/fw;
 float line=1.-smoothstep(.4,1.1,min(g.x,g.y));
 return mix(col,vec3(.64,.82,.79),line*.36*uGrid);
}
#endif
`,eo=`
uniform vec4 uWaves[32];uniform vec2 uPhases[32];
float waterLevel(vec2 p){
 float depth=max(0.,uTide-beachHeight(p));float h=0.;
 for(int i=0;i<16;i++){
  vec4 w=uWaves[i];float phase=dot(p,w.xy)*w.z-uTime*uPhases[i].x+uPhases[i].y;
  float resolved=1.-smoothstep(180./w.z,500./w.z,length(p-cameraPosition.xz));
  h+=w.w*sin(phase)*resolved;
 }
 float shore=(uTide-beachHeight(p))/.055;
 float approach=sin(shore*.48-uTime*1.5+noise(p*.016)*2.);
 float shoal=exp(-pow((depth-.6)/.85,2.));
 h=h*uWave*1.7*smoothstep(0.,2.5,depth)+approach*uWave*.11*shoal;
 return uTide+h;
}
`;var qe=(re.west+re.east)*.5*w,Te=-.65*w-2.55,ke=t=>[...t],to=(t,e)=>{let o=ft(t,e);return[o[0]/1e3,-o[1]/1e3]},ft=(t,e)=>[2e3+(t-qe),e],pt=(t,e)=>[qe+t-2e3,e];function Xe(t){let e=0,o=1.7;for(let a=0;a<40;a++){let s=(e+o)/2;Math.abs(Ee(s)[1])<Math.abs(t)?e=s:o=s}return Ee((e+o)/2)[0]}var es=[Array.from({length:721},(t,e)=>be(e*2*Math.PI/720)),Array.from({length:1801},(t,e)=>Ee(-1.7+3.4*e/1800))];var mt=0,oo=pt(500,mt)[0];var gt=([t,e,o])=>{let[a,s]=pt(t,o);return[a,e+Te,s]};function vt(t,e,o,a){let s=e.map(gt),n=e.map((l,r)=>{let p=e[Math.max(0,r-1)],d=e[Math.min(e.length-1,r+1)],f=Math.hypot(d[0]-p[0],d[2]-p[2])||1;return gt([l[0]+(d[0]-p[0])/f*65,l[1]-8,l[2]+(d[2]-p[2])/f*65])}),i=s.slice(1).reduce((l,r,p)=>l+Math.hypot(...r.map((d,f)=>d-s[p][f])),0);return{name:t,title:t,description:a,walk:!0,duration:i/o+3,fov:60,positions:s,targets:n}}function ao(t){let e=Array.from({length:161},(n,i)=>{let[l,r]=be(i/160*Math.PI*2);return[l,12,r]}),o=[vt("\u5DE6\u73AF\u6F2B\u6EE9",e,6,"\u6CBF\u5DE6\u73AF\u6C99\u6EE9\u73AF\u884C \xB7 \u53EF\u968F\u65F6\u624B\u52A8\u63A5\u7BA1")];for(let[n,i]of[["\u53F3\u4E0A\u6C99\u6EE9",-1800],["\u53F3\u4E0B\u6C99\u6EE9",1800]]){let l=Array.from({length:121},(r,p)=>{let d=p/120,f=80+(i-80)*d,g=(2040-Xe(80)-40)*Math.exp(-d*20);return[Xe(f)+40+g,16,f]});o.push(vt(n,l,6,"\u4E3B\u697C\u6C99\u6EE9\u51FA\u53D1 \xB7 \u6CBF\u53F3\u6EE9\u5411"+(i<0?"\u5317":"\u5357")+"\u6F2B\u6B65 \xB7 \u53EF\u968F\u65F6\u624B\u52A8\u63A5\u7BA1"))}let a=Array.from({length:121},(n,i)=>{let l=1600-i/120*3200;return[Xe(l)+400,460,l]}),s=vt("\u66F2\u7EBF\u6D77\u5CB8\u603B\u89C8",a,30,"\u6CBF\u53F3\u4FA7\u6D77\u5CB8\u7F13\u884C\u4FEF\u77B0 \xB7 \u5DE6\u73AF\u4E0E\u5EFA\u7B51\u7FA4\u5C3D\u6536\u773C\u5E95");s.fov=72,s.targets=a.map(n=>gt([n[0]-650,3,n[2]])),o.push(s);for(let n of o){let i=t.findIndex(l=>l.name===n.name);i<0?t.push(n):t[i]=n}}function so(t,e){let o=Math.max(0,Math.min(e,t)),a=Math.min(3,e/3),s=n=>{let i=n/a;return a*(i*i*i-.5*i*i*i*i)};return o<a?s(o)/(e-a):o>e-a?1-s(e-o)/(e-a):(o-a/2)/(e-a)}function yt(t=new Date){let e=new Intl.DateTimeFormat("en-GB",{timeZone:"Asia/Shanghai",hour:"2-digit",minute:"2-digit",second:"2-digit",hourCycle:"h23"}).formatToParts(t),o=a=>Number(e.find(s=>s.type===a).value);return o("hour")+o("minute")/60+o("second")/3600}function wt(t,e,o=300){let a=Math.max(0,Math.min(1,e/o)),s=a*24,n=t+s;return{startHour:t,dayHours:s,sceneHour:(n%24+24)%24,dayOffset:Math.floor(n/24),timeRate:86400/o,cloudCoverage:.5}}var xt=Object.freeze([Object.freeze({id:"left",name:"\u5DE6\u73AF\u6F2B\u6EE9"}),Object.freeze({id:"upper",name:"\u53F3\u4E0A\u6C99\u6EE9"}),Object.freeze({id:"lower",name:"\u53F3\u4E0B\u6C99\u6EE9"})]);function ro(t=Math.random){return Object.freeze({x:(t()-.5)*256,z:(t()-.5)*256})}function no(t,e){let o=1/0;for(let n of[e.sunrise,e.sunset])if(Number.isFinite(n)){let i=((t-n)%24+36)%24-12;o=Math.min(o,Math.abs(i))}let a=Math.min(1,o/.5);return .3+.7*(a*a*a*(a*(a*6-15)+10))}function Ye(t,e,o,a=1.2){let s=Math.max(0,Math.min(.1,Number(o)||0));return t+(e-t)*-Math.expm1(-s/a)}import*as J from"../3d/vendor/three.module.js";import*as Ze from"../3d/vendor/three.module.js";import*as me from"../3d/vendor/three.module.js";import*as j from"../3d/vendor/three.module.js";import*as te from"../3d/vendor/three.module.js";var xs={steps:32,radius:2.65,width:1.65,landingDepth:1.6,upperEdge:.275*w,start:Math.PI/2,sweep:Math.PI*1.5};import*as He from"../3d/vendor/three.module.js";import*as le from"../3d/vendor/three.module.js";import*as Mt from"../3d/vendor/three.module.js";var lo={schema:"math-refuge-layout",version:2,units:"metres",origin:"original-01A-centre",axes:{east:"+X",north:"-Z"},savedAt:"2026-09-26T12:34:25.166Z",buildings:[{id:"01B",name:"\u62A5\u544A\u5385",east:-30,north:0,platformWidth:42.42640687119285,platformDepth:46.66904755831214},{id:"02",name:"\u56FE\u4E66\u9986",east:-153,north:170,platformWidth:32,platformDepth:24},{id:"03",name:"\u5171\u7814\u5DE5\u574A",east:-15,north:256,platformWidth:30,platformDepth:28},{id:"04",name:"\u6570\u5B66\u5B9E\u9A8C\u5BA4",east:-116,north:-153,platformWidth:30,platformDepth:24},{id:"05N",name:"\u5317\u98DF\u9601",east:-93,north:121,platformWidth:30,platformDepth:24},{id:"05S",name:"\u5357\u98DF\u9601",east:-27,north:-73,platformWidth:30,platformDepth:24},{id:"07",name:"\u6559\u5B66\u697C",east:-31,north:-142,platformWidth:36,platformDepth:30},{id:"R1",name:"\u4F11\u606F\u5BA4\u4E00\u7EC4",east:-28,north:68,platformWidth:26,platformDepth:20},{id:"R3",name:"\u4F11\u606F\u5BA4\u4E09\u7EC4",east:-79,north:-207,platformWidth:26,platformDepth:20},{id:"G",name:"\u6D77\u4E0A\u82B1\u56ED",east:-67,north:187,platformWidth:55,platformDepth:80},{id:"06",name:"\u8BBF\u5BA2\u5C0F\u9662",east:-196,north:215,platformWidth:36,platformDepth:28},{id:"R2",name:"\u4F11\u606F\u5BA4\u4E8C\u7EC4",east:-138,north:234,platformWidth:26,platformDepth:20},{id:"10",name:"\u72EC\u7ACB\u4F4F\u5B85",east:-1500,north:0,platformWidth:110,platformDepth:86}],assets:[],connections:[["01B","R1"],["R1","05N"],["05N","G"],["05N","02"],["02","06"],["06","R2"],["R2","03"],["03","G"],["01B","05S"],["05S","07"],["07","04"],["04","R3"],["R3","07"]],decorations:{}};var wa=39*w;var xa=[["01B","\u62A5\u544A\u5385",39,0,-62,0,30*w,33*w],["02","\u56FE\u4E66\u9986",-37,-16,-185,295,32,24],["03","\u5171\u7814\u5DE5\u574A",-6,-4,-175,175,30,28],["04","\u6570\u5B66\u5B9E\u9A8C\u5BA4",11.5,-4,-180,-170,30,24],["05N","\u5317\u98DF\u9601",39,-22,-103,171,30,24],["05S","\u5357\u98DF\u9601",-36.5,19,-103,-166,30,24],["07","\u6559\u5B66\u697C",-84,8,-185,-235,36,30],["R1","\u4F11\u606F\u5BA4\u4E00\u7EC4",-56,-28,-103,95,26,20],["R3","\u4F11\u606F\u5BA4\u4E09\u7EC4",-47,-38,-122,-110,26,20],["G","\u6D77\u4E0A\u82B1\u56ED",-43,0,-250,320,55,80],["06","\u8BBF\u5BA2\u5C0F\u9662",-56,-28,-186,355,36,28],["R2","\u4F11\u606F\u5BA4\u4E8C\u7EC4",-47,-38,-175,235,26,20]];var Ma=t=>new le.Vector3(wa+t[4]-t[2]*w,0,-t[5]-t[3]*w);var ba=xa.map(t=>{let e=lo.buildings.find(o=>o.id===t[0]);return[...t.slice(0,4),e.east,e.north,t[6],t[7]]}),Ke=t=>Ma(ba.find(e=>e[0]===t));async function Qe(t,e=()=>{},o=fetch){let a=await o(t);if(!a.ok)throw new Error(`Resource HTTP ${a.status}`);let s=Number(a.headers.get("content-length")),n=a.headers.get("content-encoding");if(!a.body?.getReader){let p=await a.blob();return e(1),p}let i=a.body.getReader(),l=[],r=0;try{for(;;){let{done:p,value:d}=await i.read();if(p)break;l.push(d),r+=d.byteLength,s>0&&!n&&e(Math.min(.99,r/s)),n||globalThis.refugeTransfer?.progress(t,r)}}finally{i.releaseLock()}return e(1),new Blob(l,{type:a.headers.get("content-type")||"application/octet-stream"})}import*as $e from"../3d/vendor/three.module.js";var uo=null,Ea=null;async function ho(t){let e=t();if(e?.next)for(;;){let o=await e.next();if(o.done)return;await(typeof o.value=="function"?o.value():o.value)}else await e}var _e=[],po=new Set,ze=new Map,mo=!1,vo=!1,Et=0,go=3,yo=0,Tt=0,wo=0,xo=0,St=new Set;function fo(){for(let t of[...St]){let e=t.phase&&ze.get(t.phase),o=t.phase?e?.done||0:t.criticalOnly?wo:yo,a=t.phase?e?.total||0:t.criticalOnly?xo:Tt;t.report(a?o/a:1),o===a&&(St.delete(t),t.resolve())}}function Rt(){for(;Et<go;){let t=a=>vo||mo&&a.critical||po.has(a.phase),e=_e.findIndex(a=>t(a)&&a.phase==="entry");if(e<0&&(e=_e.findIndex(a=>t(a)&&a.critical)),e<0&&(e=_e.findIndex(t)),e<0)break;let o=_e.splice(e,1)[0];Et++,Promise.resolve().then(()=>uo?uo(o):o.prepare?Promise.resolve(o.prepare()).then(()=>ho(o.job)):ho(o.job)).catch(()=>{}).finally(()=>{Et--,yo++,ze.get(o.phase).done++,o.critical&&wo++,fo(),setTimeout(Rt,0)})}fo()}function Mo(t=()=>{},{criticalOnly:e=!1,concurrency:o=3,phase:a=null}={}){return a?po.add(a):(mo=!0,e||(vo=!0)),go=Math.max(1,Math.min(3,o)),new Promise(s=>{St.add({report:t,resolve:s,criticalOnly:e,phase:a}),Rt()})}function At(t,{critical:e=!1,phase:o=e?"hall":"background",prepare:a=null}={}){Tt++,e&&xo++,ze.has(o)||ze.set(o,{done:0,total:0}),ze.get(o).total++,_e.push({job:t,prepare:a,critical:e,phase:o,id:Tt}),Rt()}function Pt(t,{critical:e=!1,phase:o=e?"hall":"background"}={}){let a=document.createElement("canvas");a.width=a.height=1;let s=a.getContext("2d");s.fillStyle=/normal|waternormals/.test(t)?"rgb(128,128,255)":"white",s.fillRect(0,0,1,1);let n=new $e.CanvasTexture(a),i;return At(function*(){yield()=>{i&&(n.image=i,n.needsUpdate=!0,Ea?.(n))}},{critical:e,phase:o,prepare:async()=>{try{let r=await Qe(t);if(globalThis.createImageBitmap)i=await createImageBitmap(r,{imageOrientation:"flipY",premultiplyAlpha:"none",colorSpaceConversion:"none"});else{let p=URL.createObjectURL(r);try{let d=await new $e.TextureLoader().loadAsync(p);i=d.image,d.dispose()}finally{URL.revokeObjectURL(p)}}}catch{}}}),n}import*as L from"../3d/vendor/three.module.js";import*as S from"../3d/vendor/three.module.js";var Je=`
vec2 coastCoordinates(vec2 p){
 #ifdef CURVED_COAST
 return p;
 #else
 return vec2(dot(p,vec2(.94,.341174)),dot(p,vec2(.341174,-.94)));
 #endif
}
vec3 opticalBedNormal(vec2 ca){
 #ifdef CURVED_COAST
 return normalize(vec3(beachHeight(ca-vec2(.5,0.))-beachHeight(ca+vec2(.5,0.)),1.,beachHeight(ca-vec2(0.,.5))-beachHeight(ca+vec2(0.,.5))));
 #else
 return normalize(vec3(-.052,1.,-.019));
 #endif
}
vec3 sandAlbedo(vec2 ca){
 float ripple=sin(ca.x*8.+noise(ca*.65)*3.+sin(ca.y*.8))*.5+.5;
 float filtered=1.-smoothstep(.3,1.5,length(fwidth(ca*8.)));
 float grains=noise(ca*95.);
 float gf=1.-smoothstep(.3,1.,length(fwidth(ca*95.)));
 return vec3(.48,.365,.235)*(.90+.10*noise(ca*1.8)+.045*ripple*filtered+.06*(grains-.5)*gf);
}
vec3 coastIrradiance(vec3 n){
 float day=smoothstep(5.,22.,uSun), dusk=1.-smoothstep(-3.,3.,uSun);
 vec3 ambient=mix(vec3(.22,.28,.38),vec3(.48,.64,.78),day);
 vec3 sunlight=mix(vec3(1.8,.88,.34),vec3(1.6,1.52,1.35),day);
 return ambient*(.65+.35*max(0.,n.y))*(1.-dusk*.55)
       +sunlight*max(0.,dot(n,sunDirection()))*smoothstep(-4.,3.,uSun);
}
vec3 transmittedWater(vec3 p,vec3 view,vec3 n){
 vec3 ray=refract(-view,n,1./1.333);
 // Refine intersection with the actual sloping seabed. Far paths are opaque.
 float travel=clamp((p.y-beachHeight(coastCoordinates(p.xz)))/max(.08,-ray.y),0.,60.);
 for(int i=0;i<3;i++){
  vec3 hit=p+ray*travel;vec2 ca=coastCoordinates(hit.xz);
  float residual=hit.y-beachHeight(ca);
  float slope=.055*dot(ray.xz,vec2(.94,.341174));
  #ifdef CURVED_COAST
  float probe=.5;
  slope=(beachHeight(ca+ray.xz*probe)-beachHeight(ca))/probe;
  #endif
  travel=clamp(travel+residual/max(.08,-ray.y+slope),0.,60.);
 }
 vec2 bottom=coastCoordinates((p+ray*travel).xz);
 vec3 extinction=vec3(.43,.105,.070);
 vec3 transmission=exp(-extinction*travel);
 float bottomDepth=max(0.,p.y-beachHeight(bottom));
 vec3 bottomLight=exp(-extinction*bottomDepth/max(.28,sunDirection().y));
 vec3 sand=sandAlbedo(bottom)*.57*coastIrradiance(opticalBedNormal(bottom))*bottomLight;
 float day=smoothstep(5.,22.,uSun);
 vec3 scatter=mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day);
 scatter*=.7+.3*max(0.,n.y);
 return sand*transmission+scatter*(1.-transmission);
}
`,Ct=`
 #ifdef COASTAL_OPTICS
 slope=vec2(0.);
 for(int i=0;i<9;i++){
  float band=float(i),k=9.*pow(1.55,band);
  vec2 dir=vec2(cos(band*2.399+.3),sin(band*2.399+.3));
  float packet=noise(uv*.42+band*7.1);
  float phase=dot(uv,dir)*k+packet*4.-uTime*sqrt(9.81*k+.000074*k*k*k)+band*17.31;
  float visible=1.-smoothstep(.65,2.8,fwidth(phase));
  slope+=dir*cos(phase)*visible*pow(.76,band)*(.35+.55*packet);
 }
 detail=(.035+.065*uWind)*smoothstep(.005,.18,waterThickness)*(1.-vProfile.b*.65);
 #endif
`,Dt=`
 #ifdef COASTAL_OPTICS
 body=transmittedWater(vWorld,view,n);
 // Direct sun belongs to the microfacet term, not also the reflected disk.
 reflected-=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(r-sd)))*(1.-dusk*.7);
 reflected=max(reflected,vec3(0.));
 #endif
`,kt=`
 #ifdef COASTAL_OPTICS
 float nv=max(.03,dot(n,view)),nl=max(0.,dot(n,sd));
 float variance=dot(dFdx(n),dFdx(n))+dot(dFdy(n),dFdy(n));
 float alpha2=max(.00016,pow(.10+uWind*.06,4.)+variance*.22);
 float denom=nh*nh*(alpha2-1.)+1.;
 float distribution=alpha2/(PI*denom*denom);
 float gv=2.*nv/(nv+sqrt(alpha2+(1.-alpha2)*nv*nv));
 float gl=2.*nl/max(.001,nl+sqrt(alpha2+(1.-alpha2)*nl*nl));
 col=body*(1.-fresnel)+reflection*fresnel;
 col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun);
 #endif
`,Ht=`
 #ifdef COASTAL_OPTICS
 col=sandAlbedo(vCA)*mix(1.,.57,wet)*coastIrradiance(n);
 float f=.0204+.9796*pow(1.-sat(dot(n,view)),5.);
 col=mix(col,sky(r,true),wet*f*.8);
 #endif
`;import*as I from"../3d/vendor/three.module.js";function Le(t=.45){let a=3+12*Math.max(0,Math.min(1,t)),s=[],n=Math.log(120/.65)/15;for(let r=0;r<16;r++){let p=120*Math.exp(-r*n),d=2*Math.PI/p,f=Math.sqrt(9.81*d*Math.tanh(d*8)),g=Math.sqrt(9.81*d*Math.exp(-n/2)),u=Math.sqrt(9.81*d*Math.exp(n/2)),M=.0081*9.81*9.81/Math.pow(f,5)*Math.exp(-.74*Math.pow(9.81/(a*f),4));for(let v=0;v<2;v++){let y=.2+(.15+.38*r/15)*(v===0?-1:1)+Math.sin(r*2.399+v)*.12,E=Math.sqrt(Math.max(0,M*(u-g)));s.push({x:Math.cos(y),z:Math.sin(y),k:d,omega:f,amplitude:E,phase:(r*2+v)*2.39996323+Math.sin(r*4.37+v)*2})}}let i=Math.sqrt(s.reduce((r,p)=>r+p.amplitude*p.amplitude/2,0)),l=.17/Math.max(1e-4,i);for(let r of s)r.amplitude*=l;return s}var Ta=`
uniform float uTime, uWave, uWind, uSun;
const float PI=3.14159265359;
float sat(float x){return clamp(x,0.,1.);}
float hash(vec2 p){vec3 q=fract(vec3(p.xyx)*.1031);q+=dot(q,q.yzx+33.33);return fract((q.x+q.y)*q.z);}
float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+1.),f.x),f.y);}
float fbm(vec2 p){float a=.5,v=0.;mat2 m=mat2(1.62,1.17,-1.17,1.62);for(int i=0;i<5;i++){v+=a*noise(p);p=m*p+7.3;a*=.5;}return v;}
vec3 bubbleCell(vec2 p){
 vec2 cell=floor(p),f=fract(p),nearest=vec2(0.);float d=10.;
 for(int y=-1;y<=1;y++)for(int x=-1;x<=1;x++){
  vec2 q=vec2(float(x),float(y));
  vec2 r=q+vec2(hash(cell+q),hash(cell+q+17.3))-f;
  float h=dot(r,r);if(h<d){d=h;nearest=r;}
 }
 return vec3(nearest,sqrt(d));
}
vec3 sunDirection(){float a=uSun*PI/180.;return normalize(vec3(-.08,sin(a),-cos(a)));}
vec3 sky(vec3 rd,bool clouds){
 float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun),y=max(rd.y,0.);
 vec3 sd=sunDirection();float focus=pow(max(0.,dot(rd,sd)),9.);
 vec3 zenith=mix(vec3(.105,.17,.29),vec3(.12,.37,.65),day);zenith=mix(zenith,vec3(.045,.065,.19),dusk);
 vec3 horizon=mix(vec3(.48,.39,.35),vec3(.62,.82,.91),day);horizon=mix(horizon,vec3(.34,.25,.34),dusk);
 horizon+=vec3(.60,.19,.025)*focus*(1.-day)*(1.-dusk*.65);
 vec3 col=mix(horizon,zenith,pow(sat(y),.45));
 vec3 warm=mix(vec3(1.2,.55,.15),vec3(.8,.91,1.),day);
 col+=warm*pow(focus,3.)*.22*(1.-day*.65);
 col+=mix(vec3(1.,.55,.15),vec3(.5,.62,.69),day)*exp(-pow(length(rd-sd)/.15,1.2))*.85*(1.-dusk*.6);
 if(clouds)col+=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(rd-sd)))*(1.-dusk*.7);
 if(clouds&&rd.y>0.){
  vec2 cp=rd.xz/(rd.y+.14)*1.6+vec2(uTime*.004,0.);
  float n=fbm(cp*1.35+vec2(16.7,3.)),w=fbm(cp*vec2(.9,3.5)+21.);
  float density=smoothstep(.41,.68,n*.82+w*.18)*smoothstep(0.,.07,rd.y)*.90;
  vec3 dark=mix(vec3(.065,.10,.17),vec3(.51,.64,.73),day);dark=mix(dark,vec3(.10,.10,.23),dusk);
  vec3 light=mix(vec3(1.05,.41,.15),vec3(1.,1.01,1.02),day);light=mix(light,vec3(.43,.27,.40),dusk);
  col=mix(col,mix(light,dark,smoothstep(.07,.9,sat((n-.37)*6.5)))+warm*focus*.15,density);
 }
 return col;
}
vec3 tone(vec3 x){x*=.95;return pow(clamp((x*(2.51*x+.03))/(x*(2.43*x+.59)+.14),0.,1.),vec3(.82));}
`,Sa=`
uniform sampler2D uProfile;
uniform vec4 uWaves[32];
uniform vec2 uPhases[32];
float shore(float a){return 3.4+1.4*sin(a*.023)+.38*sin(a*.093);}
vec2 worldXZ(vec2 ca){return vec2(.94*ca.x+.341174*ca.y,.341174*ca.x-.94*ca.y);}
float phaseOffset(float a){return 2.8*sin(a*.067)+1.25*sin(a*.19)+.32*sin(a*.57);}
float beachHeight(vec2 ca){return (ca.x-shore(ca.y))*.055+.012*noise(ca*.7);}
float swashReach(float a){
 float p=(uTime*2.05-phaseOffset(a)-shore(a)+1.)*.3141593;
 float pulse=clamp(.5+.5*cos(p)+.12*sin(2.*p),0.,1.);
 return -.7+3.6*pulse+.23*sin(a*.67)+.09*sin(a*1.73);
}
float swashLevel(vec2 ca){
 float edge=shore(ca.y)+swashReach(ca.y);
 return max(0.,beachHeight(ca))+.085*smoothstep(-.15,2.8,edge-ca.x);
}
vec4 profileAt(vec2 ca){
 float moving=uTime*2.05;
 float q=ca.x-moving+phaseOffset(ca.y);
 float id=floor((q+10.)/20.);
 float local=mod(q+10.,20.)-10.-(hash(vec2(id,17.))-.5)*3.;
 float center=ca.x-local;
 float bar=2.6*sin(ca.y*.13+id*1.7)+1.5*noise(vec2(ca.y*.31,id));
 float stage=clamp((center-(shore(ca.y)-27.+bar))/24.,0.,1.);
 vec4 result=texture2D(uProfile,vec2(clamp((local+10.)/20.,0.,1.),stage));
 float breakingPatch=smoothstep(.24,.78,noise(vec2(ca.y*.12,id*2.7)));
 // Most of the front spills; only short sections develop an overhanging lip.
 float smoothRidge=exp(-pow((local+.4)/3.0,2.))*.60;
 float spill=1.-smoothstep(.68,.96,stage);
 result.r*=(.25+.75*breakingPatch)*(1.-smoothstep(.74,1.,stage));
 result.g=mix(smoothRidge*spill,result.g,.35+.65*breakingPatch);
 result.g*=.65+.65*hash(vec2(id,29.));
 result.b=max(result.b,smoothstep(.36,.60,stage)*(1.-smoothstep(.85,1.,stage))*exp(-pow((local-1.)/2.3,2.)))*(.45+breakingPatch*.55);
 result*=smoothstep(-60.,-18.,center);
 return result;
}
vec3 surfaceAt(vec2 ca){
 vec4 profile=profileAt(ca);
 float d=(shore(ca.y)-ca.x)*.12;
 float heightScale=uWave*.42*(.75+.40*noise(vec2(ca.y*.18,4.)));
 float offshore=smoothstep(3.,10.,shore(ca.y)-ca.x);
 vec2 displaced=ca+vec2(profile.r*offshore,0.);
 vec3 p=vec3(worldXZ(displaced).x,profile.g*heightScale,worldXZ(displaced).y);
 p.y+=(noise(vec2(ca.y*1.3+uTime*1.1,ca.x*.9))- .5)*.075*profile.b;
 float calm=smoothstep(.1,5.,d)*(1.-profile.a*.75);
 vec2 base=worldXZ(ca);
 for(int i=0;i<32;i++){
  vec4 w=uWaves[i];float phase=dot(base,w.xy)*w.z-uPhases[i].x*uTime+uPhases[i].y;
  float wavelength=6.2831853/w.z;
  float resolved=1.-smoothstep(wavelength*7.+25.,wavelength*24.+85.,length(base-cameraPosition.xz));
  float amp=w.w*(.4+uWind*.6)*uWave*calm*resolved;
  p.xz+=w.xy*amp*.56*cos(phase);p.y+=amp*sin(phase);
 }
 // A shallow swash tongue advances and recedes after the broken front.
 float wet=smoothstep(-.3,1.8,d);
 p.y=p.y*wet+swashLevel(ca)*(1.-smoothstep(.2,1.8,d));
 return p;
}
`,Ra=`
uniform sampler2D uFoam;
float foamDensity(vec2 ca){
 vec2 uv=(ca-vec2(-35.,-45.))/vec2(60.,160.);
 float history=0.;
 if(all(greaterThan(uv,vec2(0.)))&&all(lessThan(uv,vec2(1.))))history=texture2D(uFoam,uv).r;
 float fresh=profileAt(ca).b;
 float edge=shore(ca.y)+swashReach(ca.y)-ca.x;
 float rim=exp(-pow((edge-.25)/.37,2.))*smoothstep(-2.,1.,ca.x-shore(ca.y));
 return max(history,max(fresh*.85,rim*.68))*smoothstep(-.12,.4,edge);
}
float foamLumps(vec2 ca){
 vec2 flow=ca-vec2(uTime*.65,.16*sin(uTime*.3));
 float large=noise(flow*.85+vec2(noise(flow*.32))*2.);
 float cells=noise(flow*2.1);
 return smoothstep(.29,.68,large*.72+cells*.28);
}
float foamThickness(vec2 ca){
 float density=foamDensity(ca),lumps=foamLumps(ca);
 float fresh=profileAt(ca).b;
 float rim=exp(-pow((shore(ca.y)+swashReach(ca.y)-ca.x-.3)/.5,2.));
 float h=(.015+fresh*(.16+.06*uWave)+rim*.045)*smoothstep(.08,.55,density)*lumps;
 return h;
}
vec3 whitewaterAt(vec2 ca){
 vec3 p=surfaceAt(ca);
 p.y+=foamThickness(ca)+.002;
 return p;
}
`;var bo={environment:Ta,surfaceModel:Sa,whitewaterModel:Ra};function Eo(t){let e=Math.max(0,Math.min(1,(t-25)/55));return 1-e*e*(3-2*e)}function To(t){let e=Math.max(0,Math.min(1,(t-180)/470));return 1-e*e*(3-2*e)}function So(t,e=!0){return e?t<680:t<=650}var _t=`
uniform float uOceanLevel;
vec3 grazingSea(vec3 ray){
 return sky(normalize(vec3(ray.x,.00001,ray.z)),false)*vec3(.76,.84,.89);
}
// Analytic flat-water continuation beyond the detailed mesh, in world-ray
// coordinates. Unlike a solid horizon strip, it retains view-dependent sky
// reflections, water Fresnel and the same GGX sunlight model as 02.
vec3 distantSea(vec3 ray){
 ray=normalize(ray);vec3 view=-ray,n=vec3(0.,1.,0.),sd=sunDirection();
 float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
 vec3 r=reflect(ray,n);r.y=max(.002,r.y);
 vec3 reflected=sky(r,true);
 reflected-=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(r-sd)))*(1.-dusk*.7);
 reflected=max(reflected,vec3(0.));
 float fresnel=.0204+.9796*pow(1.-sat(view.y),5.);
 vec3 body=mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day);
 vec3 col=mix(body,reflected,fresnel);
 vec3 halfV=normalize(sd+view);float nh=max(.001,halfV.y);
 float nv=max(.03,view.y),nl=max(0.,sd.y),alpha2=.00016;
 float denom=nh*nh*(alpha2-1.)+1.;float distribution=alpha2/(PI*denom*denom);
 float gv=2.*nv/(nv+sqrt(alpha2+(1.-alpha2)*nv*nv));
 float gl=2.*nl/max(.001,nl+sqrt(alpha2+(1.-alpha2)*nl*nl));
 float sf=.02+.98*pow(1.-sat(dot(view,halfV)),5.);
 vec3 light=mix(vec3(1.8,.91,.36),vec3(1.4,1.4,1.25),day)*(1.-dusk*.55);
 col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun);
 float travel=max(0.,cameraPosition.y-uOceanLevel)/max(.000001,-ray.y);
 float range=travel*length(ray.xz);
 float haze=1.-exp(-pow(range*.000015,1.2));
 return mix(col,grazingSea(ray),haze);
}
vec3 panoramicBackground(vec3 ray){
 float aa=max(fwidth(ray.y),.00003);
 if(ray.y>=aa)return sky(ray,true);
 return mix(distantSea(ray),sky(ray,true),smoothstep(-aa,aa,ray.y));
}
`,et=bo.environment,Ro=`#define COAST_FRAGMENT
`+et+dt+_t;function Aa(t=256){let e=new S.PlaneGeometry(2,2,t,t);return e.rotateX(-Math.PI/2),e}function Ao(t,e,o,a){let s=[-410,-240,-150,-90,-65,-52,-48,-40,-25,-10,0,10,25,40,48,52,65,90,150,240,410],n=[],i=[];for(let p=0;p<=e;p++){let d=o+(a-o)*p/e,f=t(d),g=t(d-1e-4),u=t(d+1e-4),M=u[0]-g[0],v=u[1]-g[1],h=Math.hypot(M,v);for(let y of s){let E=f[0]-v/h*y,T=f[1]+M/h*y;n.push(E,De(Math.abs(y),E,T),T)}}let l=s.length;for(let p=0;p<e;p++)for(let d=0;d<l-1;d++){let f=p*l+d,g=f+l;i.push(f,g,f+1,f+1,g,g+1)}let r=new S.BufferGeometry;return r.setAttribute("position",new S.Float32BufferAttribute(n,3)),r.setIndex(i),r.computeBoundingSphere(),r}var tt=class{constructor(e,o,a={}){this.renderer=a.renderer||new S.WebGLRenderer({canvas:e,antialias:!0,powerPreference:"high-performance"}),a.renderer||(this.renderer.setPixelRatio(1),this.renderer.debug.onShaderError=(f,g,u,M)=>{throw Error(f.getShaderInfoLog(u)+`
`+f.getShaderInfoLog(M))}),this.scene=new S.Scene,this.camera=new S.PerspectiveCamera(64,1,.15,18e3);let s=Le(.35);this.uniforms={uDistance:{value:o},uOrigin:{value:new S.Vector2},uNear:{value:8},uTime:{value:7.1},uWave:{value:.6},uWind:{value:.35},uSun:{value:24},uGrid:{value:0},uTide:{value:0},uOceanLevel:{value:0},uWaves:{value:s.map(f=>new S.Vector4(f.x,f.z,f.k,f.amplitude))},uPhases:{value:s.map(f=>new S.Vector2(f.omega,f.phase))}};let n=new S.Mesh(new S.SphereGeometry(15e3,32,16),new S.ShaderMaterial({uniforms:this.uniforms,side:S.BackSide,depthWrite:!1,vertexShader:"varying vec3 vRay;void main(){vRay=position;gl_Position=projectionMatrix*viewMatrix*vec4(position+cameraPosition,1.);}",fragmentShader:et+_t+"varying vec3 vRay;void main(){gl_FragColor=vec4(tone(panoramicBackground(normalize(vRay))),1.);}"}));n.frustumCulled=!1,n.renderOrder=-10,a.sky!==!1?this.scene.add(n):(n.geometry.dispose(),n.material.dispose()),this.uniforms.uInverseProjection={value:new S.Matrix4},this.uniforms.uCameraWorld={value:new S.Matrix4};let i=new S.Mesh(new S.PlaneGeometry(2,2),new S.ShaderMaterial({uniforms:this.uniforms,depthWrite:!1,depthTest:!0,vertexShader:`uniform mat4 uInverseProjection,uCameraWorld;varying vec3 vRay;
    void main(){vec4 ray=uInverseProjection*vec4(position.xy,1.,1.);vRay=mat3(uCameraWorld)*ray.xyz;gl_Position=vec4(position.xy,1.,1.);}`,fragmentShader:et+_t+`varying vec3 vRay;
    void main(){
     vec3 ray=normalize(vRay);if(ray.y>=-.0000001||cameraPosition.y<=uOceanLevel)discard;
     gl_FragColor=vec4(tone(distantSea(ray)),1.);
    }`}));i.name="Continuous far ocean background",i.frustumCulled=!1,i.renderOrder=a.backgroundOrder??-5,this.farOcean=i,this.scene.add(i);let l=new S.ShaderMaterial({uniforms:this.uniforms,defines:{COASTAL_OPTICS:1,CURVED_COAST:1},side:S.DoubleSide,vertexShader:"varying vec3 vWorld;varying vec2 vCA;void main(){vWorld=position;vCA=position.xz;gl_Position=projectionMatrix*viewMatrix*vec4(position,1.);}",fragmentShader:Ro+Je+`
    varying vec3 vWorld;varying vec2 vCA;
    void main(){
     // Distant water shades its bed analytically. Do not depth-fight a second
     // submerged sand surface when sub-metre separation is no longer resolved.
     if(length(vWorld-cameraPosition)>2000.&&vWorld.y<uTide-.12)discard;
     // Clip self-overlapping submerged ribbon skirts to their nearest curve.
     if(abs(vWorld.y-beachHeight(vCA))>.6&&vWorld.y<-.5)discard;
     float h=beachHeight(vCA),wet=1.-smoothstep(.03,.6,h-uTide-.10);
     vec3 n=bedNormal(vCA),view=normalize(cameraPosition-vWorld),r=reflect(-view,n),col=vec3(0.);
     ${Ht}
     float distance=length(cameraPosition-vWorld);
     col=mix(col,sky(normalize(vec3(-view.x,.005,-view.z)),false),min(.9,1.-exp(-distance*.00010)));
     gl_FragColor=vec4(tone(gridColor(col,vCA)),1.);
    }`});this.scene.add(new S.Mesh(Ao(be,1200,0,Math.PI*2),l)),this.scene.add(new S.Mesh(Ao(Ee,2e3,-1.7,1.7),l));let r=Aa(),p="uniform float uNear;vec2 gridPoint(vec2 p){return uOrigin+sign(p)*(exp(abs(p)*log(1.+10000./uNear))-1.)*uNear;}";this.uniforms.uFoamVisibility={value:1},this.uniforms.uBreakerVisibility={value:1};let d=new S.ShaderMaterial({uniforms:this.uniforms,defines:{COASTAL_OPTICS:1,CURVED_COAST:1,FOAM_DETAIL:1},side:S.DoubleSide,transparent:!0,depthWrite:!0,forceSinglePass:!0,vertexShader:et+dt+eo+p+`
    varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
    void main(){
     vec2 p=gridPoint(position.xz);float h=waterLevel(p);
     float e=max(.15,length(p-cameraPosition.xz)*.001);
     vNormal=normalize(vec3(waterLevel(p-vec2(e,0.))-waterLevel(p+vec2(e,0.)),2.*e,waterLevel(p-vec2(0.,e))-waterLevel(p+vec2(0.,e))));
     vWorld=vec3(p.x,h,p.y);vCA=p;vProfile=vec4(0.);gl_Position=projectionMatrix*viewMatrix*vec4(vWorld,1.);
    }`,fragmentShader:Ro+Je+`
    uniform float uFoamVisibility,uBreakerVisibility;
    uniform vec4 uWaves[32];uniform vec2 uPhases[32];
    varying vec3 vWorld,vNormal;varying vec2 vCA;varying vec4 vProfile;
    void main(){
     float bed=beachHeight(vCA),waterThickness=vWorld.y-bed;
     float coverage=smoothstep(0.,.035,waterThickness);if(coverage<.005)discard;
     vec3 view=normalize(cameraPosition-vWorld),n=normalize(vNormal);
     if(n.y<0.)n=-n;
     float distance=length(cameraPosition-vWorld);vec2 uv=vWorld.xz,slope=vec2(0.);float detail=0.;
     // Short gravity waves are too small for the adaptive geometry. Retain
     // their moving normals until their wavelength becomes subpixel.
     vec2 gravitySlope=vec2(0.);
     for(int i=16;i<32;i++){
      vec4 w=uWaves[i];float phase=dot(uv,w.xy)*w.z-uTime*uPhases[i].x+uPhases[i].y;
      float visible=1.-smoothstep(.8,3.,fwidth(phase));
      gravitySlope+=w.xy*w.z*w.w*cos(phase)*visible;
     }
     n=normalize(n+vec3(-gravitySlope.x,0.,-gravitySlope.y)*uWave*1.7*smoothstep(0.,2.5,waterThickness));
     ${Ct}
     n=normalize(n+vec3(-slope.x,0.,-slope.y)*detail);
     vec3 sd=sunDirection(),r=reflect(-view,n);r.y=max(.002,r.y);
     float day=smoothstep(5.,22.,uSun),dusk=1.-smoothstep(-3.,3.,uSun);
     float fresnel=.0204+.9796*pow(1.-sat(dot(view,n)),5.);
     vec3 reflected=sky(r,true),body=vec3(0.);
     ${Dt}
     vec3 reflection=reflected,col=body;vec3 halfV=normalize(sd+view);
     float nh=max(.001,dot(n,halfV));float sf=.02+.98*pow(1.-sat(dot(view,halfV)),5.);
     vec3 light=mix(vec3(1.8,.91,.36),vec3(1.4,1.4,1.25),day)*(1.-dusk*.55);
     ${kt}
     #if FOAM_DETAIL == 1
     // Derivatives outside the varying branch: only resolved shallow foam
     // evaluates noise/crest/exponential terms. Remote fragments skip them.
     float footprint=max(length(dFdx(vCA)),length(dFdy(vCA)))*1.8;
     float foamLOD=uFoamVisibility*(1.-smoothstep(.35,1.25,footprint))*(1.-smoothstep(60.,180.,distance));
     float shorePhase=(uTide-bed)/.055*.48-uTime*1.5;
     float breakerLOD=uBreakerVisibility*(1.-smoothstep(1.,3.,fwidth(shorePhase)))*(1.-smoothstep(450.,1600.,distance));
     if(max(foamLOD,breakerLOD)>.001&&waterThickness<2.){
      float shore=(uTide-bed)/.055;
      float band=pow(.5+.5*sin(shorePhase+noise(vCA*.016)*2.),3.);
      float foam=band*exp(-pow((waterThickness-.45)/.7,2.))*.12*breakerLOD;
      if(foamLOD>.001){
       float crest=pow(.5+.5*sin(shore*.48-uTime*1.5+noise(vCA*.016)*2.),10.);
       float foamPatch=smoothstep(.35,.70,noise(vCA*1.8+uTime*.18));
       float fine=(exp(-pow((waterThickness-.06)/.13,2.))*.45+crest*exp(-pow((waterThickness-.45)/.7,2.))*.2)*foamPatch;
       foam=mix(foam,fine,foamLOD);
      }
      vec3 white=mix(vec3(.65,.63,.57),vec3(.97,1.,.94),day);
      col=mix(col,white,foam*smoothstep(0.,.05,waterThickness));
     }
     #endif
     float horizontalDistance=length(vCA-cameraPosition.xz);
     float haze=1.-exp(-pow(horizontalDistance*.000015,1.2));
     col=mix(col,grazingSea(-view),haze);
     float horizonBlend=smoothstep(6500.,9500.,horizontalDistance);
     col=mix(col,distantSea(-view),horizonBlend);
     gl_FragColor=vec4(tone(gridColor(col,vCA)),coverage);
    }`});this.water=new S.Mesh(r,d),this.water.frustumCulled=!1,this.water.renderOrder=1,this.scene.add(this.water),this.waterNear=d,this.waterFar=d.clone(),this.waterFar.uniforms=this.uniforms,this.waterFar.defines={...d.defines,FOAM_DETAIL:0},this.foamDetail=!0}resize(e,o){this.renderer.setSize(e,o,!1),this.camera.aspect=e/o,this.camera.updateProjectionMatrix()}draw(e,o={}){this.uniforms.uTime.value=e.time,this.uniforms.uSun.value=e.sun,this.uniforms.uWave.value=e.wave,this.uniforms.uTide.value=Jt(e),this.uniforms.uOceanLevel.value=this.uniforms.uTide.value;let a=Math.max(0,this.camera.position.y-this.uniforms.uTide.value),s=Math.max(.15,a*.003),n=Math.max(18e3,a+16e3);(this.camera.near!==s||this.camera.far!==n)&&(this.camera.near=s,this.camera.far=n,this.camera.updateProjectionMatrix()),this.camera.updateMatrixWorld(),this.uniforms.uInverseProjection.value.copy(this.camera.projectionMatrixInverse),this.uniforms.uCameraWorld.value.copy(this.camera.matrixWorld),this.uniforms.uFoamVisibility.value=Eo(a),this.uniforms.uBreakerVisibility.value=To(a),this.foamDetail=So(a,this.foamDetail),this.water.material=this.foamDetail?this.waterNear:this.waterFar,this.renderer.domElement.dataset.foamDetail=this.foamDetail?"near":"off",this.renderer.domElement.dataset.foamVisibility=this.uniforms.uFoamVisibility.value.toFixed(3),this.renderer.domElement.dataset.breakerVisibility=this.uniforms.uBreakerVisibility.value.toFixed(3),this.renderer.domElement.dataset.cameraHeight=a.toFixed(1),this.renderer.domElement.dataset.cameraFar=n.toFixed(1),this.uniforms.uGrid.value=e.view==="plan"?1:0,this.uniforms.uOrigin.value.set(this.camera.position.x,this.camera.position.z),this.uniforms.uNear.value=Math.max(8,this.camera.position.y*.15),o.render!==!1&&this.renderer.render(this.scene,this.camera)}};function Po(t){let e=document.createElement("canvas");e.width=t.width,e.height=t.height;let o=e.getContext("2d",{willReadFrequently:!0});o.drawImage(t,0,0);let{data:a}=o.getImageData(0,0,t.width,t.height),s=t.width,n=t.height,i=(l,r)=>(a[(r*s+l)*4]*256+a[(r*s+l)*4+1])*.01;return(l,r)=>{let p=(l-ce.minX)/ce.size*s-.5,d=(r-ce.minZ)/ce.size*n-.5;if(p<0||p>=s-1||d<0||d>=n-1)return 400;let f=Math.floor(p),g=Math.floor(d),u=p-f,M=d-g;return(1-M)*((1-u)*i(f,g)+u*i(f+1,g))+M*((1-u)*i(f,g+1)+u*i(f+1,g+1))}}async function Co(t,e,o,a=()=>{}){let s=await Qe(new URL("../ocean/elliptic-distance.png",import.meta.url),m=>a(m*.55)),n=URL.createObjectURL(s),i;try{i=await new L.TextureLoader().loadAsync(n)}finally{URL.revokeObjectURL(n)}a(.7),await new Promise(m=>setTimeout(m,16)),i.flipY=!1,i.colorSpace=L.NoColorSpace,i.minFilter=i.magFilter=L.LinearFilter,i.generateMipmaps=!1;let l=Po(i.image),r=new tt(null,i,{renderer:t,sky:!1,backgroundOrder:1001});a(.9),await new Promise(m=>setTimeout(m,16));let p=new L.Matrix4().set(1,0,0,qe-2e3,0,1,0,Te,0,0,1,0,0,0,0,1),d=p.clone().invert(),f=new L.Quaternion().setFromRotationMatrix(d),g=new L.Group;g.name="01 \xB7 elliptic coast \xB7 main hall (2 km, 0 km)";let u={studyView:{value:new L.Matrix4},studyCamera:{value:new L.Vector3},studySun:{value:new L.Vector3},studyMatrix:{value:p},studySky:o.skyMap,studyPhysical:o.skyPhysical,studySkyPrevious:o.skyPrevious??={value:o.skyMap.value},studySkyBlend:o.skyBlend??={value:1},studyMotion:{value:new L.Vector2},studyFrameDelta:{value:1/60},studyNight:o.nightVisibility,studyCloud:o.skyCloudMap,studyCloudPrevious:o.skyCloudPrevious,studyCloudBlend:o.skyCloudBlend,studyCloudEnabled:o.skyCloudEnabled,studyReflection:o.reflectionDetail};u.studySunReflection=o.sunReflection,u.studySunStrength=o.sunStrength,Object.assign(r.uniforms,u);let M=`uniform mat4 studyView,studyMatrix;uniform vec3 studyCamera,studySun;uniform sampler2D studySky,studySkyPrevious,studyCloud,studyCloudPrevious;uniform vec2 studyMotion;uniform float studySkyBlend,studyFrameDelta,studyPhysical;uniform float studyNight,studyCloudBlend,studyCloudEnabled,studyReflection;
`;r.farOcean.material.transparent=!0;let v=new Set([r.waterNear,r.waterFar,...r.scene.children.map(m=>m.material)]);for(let m of v){for(let R of["vertexShader","fragmentShader"]){let c=m[R].replaceAll("cameraPosition","studyCamera").replaceAll("viewMatrix","studyView");if(c=c.replaceAll("col+=light*min(18.,distribution*sf*gv*gl/(4.*nv))*smoothstep(-4.,1.,uSun);","float solarHighlight=distribution*sf*gv*gl/(4.*nv);col+=light*(1.05*solarHighlight/(1.05+solarHighlight))*smoothstep(-4.,1.,uSun)*studySunReflection*studySunStrength*studySolarTransmission();"),c=c.replace(/vec3 sunDirection\(\)\{[^}]*\}/,"vec3 sunDirection(){return normalize(studySun);}"),c=c.replace(/vec3 sky\(vec3 rd,bool clouds\)\{[\s\S]*?\n\}\n(?=vec3 tone)/,`vec3 skyAt(vec3 rd,bool clouds,vec3 surface){vec3 d=normalize(mat3(studyMatrix)*rd);d.y=max(.002,d.y);vec2 uv=vec2(.5+atan(d.z,d.x)/6.2831853,sqrt(clamp(asin(d.y)/1.5707963,0.,1.)));vec3 col=mix(texture2D(studySkyPrevious,uv).rgb,texture2D(studySky,uv).rgb,studySkyBlend);col=mix(vec3(.07,.24,.43)*studyNight,col,studyPhysical);if(clouds&&studyReflection>.5){vec3 worldSurface=(studyMatrix*vec4(surface,1.)).xyz;vec3 worldEye=(studyMatrix*vec4(studyCamera,1.)).xyz;
float cloudTravel=max(0.,2300.-worldSurface.y)/max(.002,d.y);
vec3 cloudRay=normalize(worldSurface+d*cloudTravel-worldEye);vec2 cloudUV=vec2(.5+atan(cloudRay.z,cloudRay.x)/6.2831853,sqrt(clamp(asin(clamp(cloudRay.y,0.,1.))/1.5707963,0.,1.)));
vec4 c=mix(texture2D(studyCloudPrevious,cloudUV),texture2D(studyCloud,cloudUV),studyCloudBlend);col=col*(1.-c.a*studyCloudEnabled)+c.rgb*studyCloudEnabled;}return col+vec3(.012,.016,.025)*(1.-smoothstep(-10.,0.,uSun));}
vec3 sky(vec3 rd,bool clouds){return skyAt(rd,clouds,studyCamera);}
`),R==="fragmentShader"){c=`float studySolarTransmission(){
      vec3 d=normalize(mat3(studyMatrix)*studySun);
      vec2 uv=vec2(.5+atan(d.z,d.x)/6.2831853,sqrt(clamp(asin(clamp(d.y,0.,1.))/1.5707963,0.,1.)));
      float opacity=mix(texture2D(studyCloudPrevious,uv).a,texture2D(studyCloud,uv).a,studyCloudBlend);
      return clamp(1.-opacity*studyCloudEnabled,0.,1.);
    }
`+c,c=c.replace("vec3 reflected=sky(r,true),body=vec3(0.);","vec3 reflected=skyAt(r,true,vWorld),body=vec3(0.);"),c=c.replace("vec3 reflected=sky(r,true);","vec3 surface=studyCamera+ray*(max(0.,studyCamera.y-uOceanLevel)/max(.000001,-ray.y));vec3 reflected=skyAt(r,true,surface);"),c=c.replace("vec3 reflected=sky(r,true),body=vec3(0.);","vec3 reflected=skyAt(r,true,vWorld),body=vec3(0.);"),c=c.replace("vec3 reflected=sky(r,true);","vec3 surface=studyCamera+ray*(max(0.,studyCamera.y-uOceanLevel)/max(.000001,-ray.y));vec3 reflected=skyAt(r,true,surface);"),c=c.replace("gl_FragColor=vec4(tone(distantSea(ray)),1.);","gl_FragColor=vec4(tone(distantSea(ray)),smoothstep(0.,.014,-ray.y));"),c=c.replace("false)*vec3(.76,.84,.89);","false)*vec3(.97,.985,1.);"),c=c.replaceAll("mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day)","mix(vec3(.009,.012,.018),mix(vec3(.014,.092,.105),vec3(.025,.24,.255),day),smoothstep(-10.,4.,uSun))"),c=c.replace("vec3 ambient=mix(vec3(.22,.28,.38),vec3(.48,.64,.78),day);","vec3 ambient=mix(vec3(.050,.055,.065),mix(vec3(.22,.28,.38),vec3(.48,.64,.78),day),smoothstep(-10.,4.,uSun));"),c=c.replace("n=normalize(vNormal)","n=vec3(0.,1.,0.)"),c=c.replace("vec2 gravitySlope=vec2(0.);","vec2 gravitySlope=vec2(0.);float unresolvedSlope=0.;"),c=c.replace("for(int i=16;i<32;i++)","for(int i=0;i<32;i++)"),c=c.replace("float visible=1.-smoothstep(.8,3.,fwidth(phase));",`float travel=abs(dot(studyMotion,w.xy)*w.z)+studyFrameDelta*abs(uPhases[i].x);
      float visible=(1.-smoothstep(.45,2.,fwidth(phase)))*(1.-smoothstep(.4,2.,travel));
      unresolvedSlope+=.5*pow(w.z*w.w*uWave*1.7,2.)*(1.-visible*visible);`),c=c.replace("float visible=1.-smoothstep(.65,2.8,fwidth(phase));","float visible=(1.-smoothstep(.45,2.,fwidth(phase)))*(1.-smoothstep(.35,2.2,studyFrameDelta*sqrt(9.81*k+.000074*k*k*k)));"),c=c.replace("max(.00016,pow(.10+uWind*.06,4.)+variance*.22)","max(.0004,pow(.10+uWind*.06,4.)+variance*.5+unresolvedSlope*.5)"),c=c.replace("nl=max(0.,sd.y),alpha2=.00016","nl=max(0.,sd.y),alpha2=.0045"),c=c.replaceAll("reflected-=vec3(5.,3.75,1.85)*(1.-smoothstep(.009,.012,length(r-sd)))*(1.-dusk*.7);",""),c=c.replace("smoothstep(450.,1600.,distance)","smoothstep(120.,650.,distance)"),c=c.replace("float band=pow(.5+.5*sin(shorePhase+noise(vCA*.016)*2.),3.);",`vec2 breakerUV=vCA+vec2(.21,-.08)*uTime;
      vec2 warp=vec2(noise(breakerUV*.035),noise(breakerUV*.047+17.))*9.;
      float pulse=pow(.5+.5*sin(shorePhase+noise(breakerUV*.08)*7.),8.);
      float islands=smoothstep(.48,.72,noise((breakerUV+warp)*.19));
      float band=pulse*islands*(.35+.65*noise(breakerUV*.61));`),c=c.replace("vec3 white=mix(vec3(.65,.63,.57),vec3(.97,1.,.94),day);","vec3 white=min(vec3(1.),sky(vec3(.2,.95,.12),false)*.65+vec3(.45,.42,.37)*smoothstep(-3.,10.,uSun));"),c=c.replace("float foamPatch=smoothstep(.35,.70,noise(vCA*1.8+uTime*.18));",`vec2 foamUV=vCA+vec2(.24,-.11)*uTime;
       float foamPatch=smoothstep(.48,.72,noise(foamUV*.85+noise(foamUV*.13)*2.));
       foamPatch*=smoothstep(.22,.65,noise(foamUV*3.7));`),c=c.replace("float fine=(exp(-pow((waterThickness-.06)/.13,2.))*.45+crest*exp(-pow((waterThickness-.45)/.7,2.))*.2)*foamPatch;","float fine=(exp(-pow((waterThickness-.055)/.09,2.))*.25+crest*exp(-pow((waterThickness-.35)/.45,2.))*.22)*foamPatch*(.3+.7*crest);"),c=c.replace("float foam=band*exp(-pow((waterThickness-.45)/.7,2.))*.12*breakerLOD;","float foam=band*exp(-pow((waterThickness-.45)/.7,2.))*.08*breakerLOD*smoothstep(.32,.68,noise(vCA*.08+uTime*.025));"),c=c.replace(/vec3 tone\(vec3 x\)\{[^}]*\}/,"vec3 tone(vec3 x){return x;}");let D=c.lastIndexOf("}");c=c.slice(0,D)+`
#include <tonemapping_fragment>
#include <colorspace_fragment>
`+c.slice(D)}m[R]=`uniform float studySunReflection,studySunStrength;
`+M+c}m.needsUpdate=!0}let h=[3,6,9].map((m,R)=>[r.waterNear,r.waterFar].map(c=>{if(R===2)return c;let D=c.clone();return D.uniforms=r.uniforms,D.fragmentShader=D.fragmentShader.replace("i<9;i++","i<"+m+";i++").replace("i<32;i++","i<"+(R===0?24:28)+";i++"),v.add(D),D}));r.water.renderOrder=-100;for(let m of[...r.scene.children])m.frustumCulled=!1,m.raycast=()=>{},g.add(m);e.add(g),a(1);let y={tide:2.55,tidal:!0,grid:!1,paused:!1},E=new L.DataTexture(new Uint8Array(4),1,1);E.needsUpdate=!0;let T=7.1,_=2,z=-1,P=null,O=null;return{async prepare(m=()=>{},R=()=>Promise.resolve()){let c=new L.Scene,D=0;for(let U of h)for(let K of U){await R();let k=new L.Mesh(r.water.geometry,K);c.add(k),await t.compileAsync?.(c,r.camera),c.remove(k),m(++D/(h.length*2)),await new Promise(b=>setTimeout(b,0))}},root:g,settings:y,initialized:!0,foam:{value:E},setEnabled(){g.visible=!0},setQuality(m){_=m},ground(m,R){let c=ft(m,R);return De(l(...c),...c)+Te},update(m,R){O?u.studyMotion.value.set(m.position.x-O.x,m.position.z-O.z):O=m.position.clone(),O.copy(m.position),u.studyFrameDelta.value+=(Math.max(1/240,Math.min(.1,R))-u.studyFrameDelta.value)*(1-Math.exp(-Math.max(0,R)*4)),y.paused||(T+=Math.max(0,Math.min(.1,R)));let c=Math.round(Math.min(1,o.windSpeed.value*o.windWaves.value/14)*20)/20;c!==z&&(z=c,P=Le(c));let D=1-Math.exp(-Math.max(0,R)/2);P.forEach((U,K)=>{let k=r.uniforms.uWaves.value[K];k.w+=(U.amplitude-k.w)*D}),r.uniforms.uWind.value+=(c-r.uniforms.uWind.value)*D,r.camera.copy(m),r.camera.position.copy(m.position).applyMatrix4(d),r.camera.quaternion.copy(m.quaternion).premultiply(f),u.studyCamera.value.copy(r.camera.position),u.studySun.value.copy(o.sunDirection.value).transformDirection(d),r.draw({time:T,tide:y.tide,tidal:y.tidal,wave:o.waveStrength.value*1.2,wind:.35,sun:Math.asin(Math.max(-1,Math.min(1,o.sunDirection.value.y)))*180/Math.PI,view:y.grid?"plan":"aerial"},{render:!1}),u.studyView.value.copy(r.camera.matrixWorldInverse),(m.near!==r.camera.near||m.far!==r.camera.far)&&(m.near=r.camera.near,m.far=r.camera.far,m.updateProjectionMatrix()),_<2&&(r.uniforms.uFoamVisibility.value=0),r.water.material=h[_][r.foamDetail?0:1],o.oceanLevel.value=r.uniforms.uTide.value+Te,o.oceanStudy.value=1,t.domElement.dataset.coastCoordinates=to(m.position.x,m.position.z).map(U=>U.toFixed(3)).join(","),t.domElement.dataset.coastTide=r.uniforms.uTide.value.toFixed(2)},dispose(){g.traverse(m=>m.geometry?.dispose());for(let m of v)m.dispose();i.dispose(),E.dispose(),e.remove(g)}}}var zt=Math.PI/180;function Pa(t){let e=Math.max(-.5,Math.min(89.9,t));return Math.max(0,1/Math.tan((e+7.31/(e+4.4))*zt)/60)}function Ca(t){let e=t,o=t+1.1;for(let a=0;a<32;a++){let s=(e+o)/2;s-Pa(s)<t?e=s:o=s}return(e+o)/2}function Lt(t){let e=Ca(Math.asin(t[1])/zt)*zt,o=Math.hypot(t[0],t[2]);return[t[0]/Math.max(o,1e-9)*Math.cos(e),Math.sin(e),t[2]/Math.max(o,1e-9)*Math.cos(e)]}var Do=`float solarRefraction(float elevation){float h=clamp(degrees(elevation),-.5,89.9);return radians(max(0.,1./tan(radians(h+7.31/(h+4.4)))/60.));}
vec3 unrefractSunRay(vec3 d){float apparent=asin(clamp(d.y,-1.,1.));float h=apparent-solarRefraction(apparent);return vec3(normalize(d.xz+vec2(1e-9)).x*cos(h),sin(h),normalize(d.xz+vec2(1e-9)).y*cos(h));}`;var It={low:{size:384,steps:24,interval:650},medium:{size:640,steps:32,interval:450},high:{size:1024,steps:48,interval:300}};var Vt=new Map;var yr=16*1024*1024,Da=(t,e)=>{let o=new URL(String(t),e);return o.search="",o.hash="",o.href};function ko(t,e=globalThis.location?.href){if(!e)return null;let o;try{o=Da(t,e)}catch{return null}let a=Vt.get(o);if(!a)return null;Vt.delete(o),Vt.set(o,a);let s=a.encoding==="base64"?Uint8Array.from(atob(a.body),n=>n.charCodeAt(0)):a.body;return new Response(s,{headers:{"Content-Type":a.type}})}function ka(t,{idleTimeout:e=15e3,totalTimeout:o=0,api:a=globalThis,concurrency:s=6,backgroundLimit:n=2}={}){if(t.resourceBounded)return t;let i=async(g,u={},M=()=>{})=>{let v=new AbortController,h=u.signal||g?.signal,y,E,T,_,z=!1,P,O=new Promise((k,b)=>P=b);O.catch(()=>{});let m=()=>{a.clearTimeout(y),a.clearTimeout(E),h?.removeEventListener("abort",D)},R=()=>{z||(z=!0,m(),M())},c=k=>{if(!z){R(),P(k),v.abort(k),T?.cancel(k).catch(()=>{});try{_?.error(k)}catch{}}},D=()=>c(h.reason||new DOMException("\u8BF7\u6C42\u5DF2\u53D6\u6D88","AbortError")),U=()=>c(new DOMException("\u8D44\u6E90\u4E0B\u8F7D\u505C\u6EDE\uFF0C\u8BF7\u91CD\u8BD5\u3002","TimeoutError")),K=()=>{a.clearTimeout(y),y=a.setTimeout(U,u.resourceIdleTimeout??e)};h?.addEventListener("abort",D,{once:!0}),K(),o>0&&(E=a.setTimeout(U,o)),h?.aborted&&D();try{if(v.signal.aborted)throw v.signal.reason;let k=await Promise.race([t(g,{...u,signal:v.signal}),O]);if(!k.ok||!k.body)return R(),k;T=k.body.getReader(),K();let b=new ReadableStream({start(N){_=N},async pull(N){try{let{done:$,value:ie}=await Promise.race([T.read(),O]);if($){R(),N.close(),T.releaseLock();return}K(),N.enqueue(ie)}catch($){R();try{N.error($)}catch{}}},cancel(N){return R(),v.abort(N),T.cancel(N)}},{highWaterMark:0}),B=new Response(b,{status:k.status,statusText:k.statusText,headers:k.headers});return Object.defineProperties(B,{url:{value:k.url},redirected:{value:k.redirected},type:{value:k.type}}),B}catch(k){throw R(),k.name==="TypeError"?new Error("\u8D44\u6E90\u4E0B\u8F7D\u5931\u8D25\uFF0C\u8BF7\u68C0\u67E5\u8FDE\u63A5\u540E\u91CD\u8BD5\u3002",{cause:k}):k}},l=[],r=0,p=0,d=()=>{for(;r<s;){let g=l.findIndex(M=>!M.low||p<n);if(g<0)return;let u=l.splice(g,1)[0];u.parent?.removeEventListener("abort",u.cancel),r++,u.low&&p++,i(u.input,u.options,()=>{r--,u.low&&p--,queueMicrotask(d)}).then(u.resolve,u.reject)}},f=(g,u={})=>new Promise((M,v)=>{let h=u.signal||g?.signal;if(h?.aborted){v(h.reason||new DOMException("\u8BF7\u6C42\u5DF2\u53D6\u6D88","AbortError"));return}let y={input:g,options:u,resolve:M,reject:v,parent:h,low:u.priority==="low"};y.cancel=()=>{let E=l.indexOf(y);E>=0&&(l.splice(E,1),h?.removeEventListener("abort",y.cancel),v(h.reason||new DOMException("\u8BF7\u6C42\u5DF2\u53D6\u6D88","AbortError")))},h?.addEventListener("abort",y.cancel,{once:!0}),l.push(y),l.sort((E,T)=>Number(E.low)-Number(T.low)),d()});return f.promote=g=>{let u=String(g),M=!1;for(let v of l)String(v.input)===u&&(v.low=!1,v.options={...v.options,priority:"high"},M=!0);return M&&(l.sort((v,h)=>Number(v.low)-Number(h.low)),d()),M},f.resourceBounded=!0,f}var Ot=new WeakMap;function Ho(t,e){if(e?.signal?.aborted)return Promise.reject(e.signal.reason||new DOMException("\u8BF7\u6C42\u5DF2\u53D6\u6D88","AbortError"));let o=ko(t?.url||t);if(o)return Promise.resolve(o);let a=globalThis.fetch,s=Ot.get(a);return s||(s=ka(a),Ot.set(a,s)),s(t,e)}Ho.promote=t=>{let e=globalThis.fetch,o=Ot.get(e)?.promote?.(t)||!1,a=e.promote?.(t)||!1;return o||a};import*as V from"../3d/vendor/three.module.js";import{BoxGeometry as Ar,Vector3 as Ha}from"../3d/vendor/three.module.js";var Pr=new Ha;var ne={origin:[oo,0,mt],halfWidth:55,halfDepth:43,floor:.9,roof:5.2};var ue=(t,e,o,a)=>({name:t,title:t,description:a,duration:28,fov:58,residence:!0,positions:[e,e].map(s=>[(s[0]+ne.origin[0])/w,s[1]/w,(s[2]+ne.origin[2])/w]),targets:[o,o].map(s=>[(s[0]+ne.origin[0])/w,s[1]/w,(s[2]+ne.origin[2])/w])}),_o=[ue("\u6D77\u4E0A\u4F4F\u5B85",[44,21,46],[0,2,0],"\u5DE6\u73AF\u5185\u6E7E\u4F4F\u5B85 \xB7 \u72EC\u7ACB\u5EAD\u9662\u4E0E\u73AF\u6C34\u9732\u53F0 \xB7 \u77F3\u3001\u6728\u4E0E\u6D77\u98CE"),ue("\u4F4F\u5B85\u7384\u5173",[3,2.55,12],[0,2.3,0],"\u5B66\u672F\u8DB3\u8FF9 \xB7 \u4ECE\u65B0\u52A0\u5761\u5230\u4E0A\u6D77"),ue("\u4F4F\u5B85\u4E66\u623F",[-9.5,2.5,-5.2],[-13,2.05,-12],"\u7814\u7A76\u4E66\u67B6 \xB7 \u8BBA\u6587\u4E0E\u9884\u5370\u672C \xB7 \u6D77\u666F\u4E66\u684C"),ue("\u4F4F\u5B85\u5C55\u5ECA",[1.5,2.5,-7],[0,2.3,-12],"\u53EF\u89C6\u5316\u6536\u85CF \xB7 \u6570\u5B66\u7ED3\u6784\u7684\u7A7A\u95F4\u8868\u8FBE"),ue("\u4F4F\u5B85\u5DE5\u4F5C\u5BA4",[15.5,2.5,-7.4],[11.5,2.05,-11.7],"AI4Math \xB7 msreader \xB7 AI4Games"),ue("\u4F4F\u5B85\u5BA2\u5385",[16.5,2.5,12],[10,1.8,7],"\u4F1A\u5BA2\u4E0E\u4EA4\u6D41 \xB7 \u6696\u6728\u3001\u7EC7\u7269\u4E0E\u5EAD\u9662"),ue("\u4F4F\u5B85\u5957\u623F",[-9.2,2.5,12],[-13,1.65,8.5],"\u5B89\u9759\u7684\u751F\u6D3B\u7A7A\u95F4 \xB7 \u8863\u5E3D\u4E0E\u72EC\u7ACB\u6D74\u5BA4"),ue("\u4F4F\u5B85\u9732\u53F0",[11,2.5,20],[27,1.1,8],"\u6D77\u666F\u8336\u5E2D \xB7 \u6D45\u6C34\u5EAD\u9662 \xB7 \u65E5\u51FA")],zo=[["\u7384\u5173 \xB7 \u5B66\u672F\u8DB3\u8FF9","\u4F4F\u5B85\u7384\u5173"],["\u4E66\u623F \xB7 \u8BBA\u6587\u6536\u85CF","\u4F4F\u5B85\u4E66\u623F"],["\u5C55\u5ECA \xB7 \u6570\u5B66\u53EF\u89C6\u5316","\u4F4F\u5B85\u5C55\u5ECA"],["\u5DE5\u4F5C\u5BA4 \xB7 AI \u4E0E\u6E38\u620F","\u4F4F\u5B85\u5DE5\u4F5C\u5BA4"],["\u4F1A\u5BA2\u5385 \xB7 \u4EA4\u6D41","\u4F4F\u5B85\u5BA2\u5385"],["\u4E3B\u5367\u5957\u623F","\u4F4F\u5B85\u5957\u623F"],["\u6D77\u666F\u9732\u53F0","\u4F4F\u5B85\u9732\u53F0"]].map(([t,e])=>({name:t,shot:e}));import*as Se from"../3d/vendor/three.module.js";import*as x from"../3d/vendor/three.module.js";import*as oe from"../3d/vendor/three.module.js";import*as he from"../3d/vendor/three.module.js";import{ShaderChunk as Vo}from"../3d/vendor/three.module.js";var Io=`
  float lightDistanceSquared = dot( lVector, lVector );
  if ( LIGHT.distance > 0.0 && lightDistanceSquared >= LIGHT.distance * LIGHT.distance ) {
    light.color = vec3( 0.0 ); light.direction = vec3( 0.0, 1.0, 0.0 ); light.visible = false; return;
  }`,$r=Vo.lights_pars_begin.replace("vec3 lVector = pointLight.position - geometryPosition;","vec3 lVector = pointLight.position - geometryPosition;"+Io.replaceAll("LIGHT","pointLight")).replace("vec3 lVector = spotLight.position - geometryPosition;","vec3 lVector = spotLight.position - geometryPosition;"+Io.replaceAll("LIGHT","spotLight")),Jr=Vo.lights_fragment_begin.replaceAll("RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight );","if ( directLight.visible ) { RE_Direct( directLight, geometryPosition, geometryNormal, geometryViewDir, geometryClearcoatNormal, material, reflectedLight ); }");var an=Ke("01B"),sn=Ke("07");import*as ve from"../3d/vendor/three.module.js";import*as C from"../3d/vendor/three.module.js";var st=(t,e,o)=>{let a=Math.max(0,Math.min(1,(o-t)/(e-t)));return a*a*(3-2*a)},Ft=t=>t-Math.floor(t);function ot(t,e){let o=Ft(t*.1031),a=Ft(e*.1031),s=o,n=o*(a+33.33)+a*(s+33.33)+s*(o+33.33);return o+=n,a+=n,s+=n,Ft((o+a)*s)}function at(t,e){let o=Math.floor(t),a=Math.floor(e),s=st(0,1,t-o),n=st(0,1,e-a);return(ot(o,a)*(1-s)+ot(o+1,a)*s)*(1-n)+(ot(o,a+1)*(1-s)+ot(o+1,a+1)*s)*n}function Ia(t,e){let o=t+at(t*.031,e*.031)*8,a=e+at(t*.027+19,e*.027+19)*8;return .68*at(o*.065,a*.065)+.32*at(o*.151+37,a*.151+37)}function Va(){return 0}function Oo(t,e=[0,0]){let o=[],a=0,s=0;for(let n=0;n<4096;n++){let i=60*Math.sqrt((n+.5)/4096),l=n*2.399963229728653,r=i*Math.cos(l),p=i*Math.sin(l),d=Va(r,p,t);if(s++,d>0){a++;continue}o.push(Ia(r-e[0],p-e[1]))}return{samples:o,total:s,excluded:a,eligible:o.length}}function Gt(t,e){if(e<=0)return 1.1;if(e>=1)return-.1;let o=-.1,a=1.1;for(let s=0;s<18;s++){let n=(o+a)/2;t.samples.reduce((l,r)=>l+st(n-.035,n+.035,r),0)/Math.max(1,t.eligible)>e?o=n:a=n}return(o+a)/2}function Bo(t){return t*(.5+.5*st(.78,.8,t))}import*as A from"../3d/vendor/three.module.js";function Oa(t=64){let e=new Uint8Array(t*t*t*4),o=(n,i,l)=>{let r=Math.imul(n,374761393)^Math.imul(i,668265263)^Math.imul(l,2147483647);return r=Math.imul(r^r>>>13,1274126177),((r^r>>>16)>>>0)/4294967296},a=(n,i,l,r)=>{let p=Math.floor(n),d=Math.floor(i),f=Math.floor(l),g=y=>y*y*(3-2*y),u=g(n-p),M=g(i-d),v=g(l-f),h=0;for(let y=0;y<2;y++)for(let E=0;E<2;E++)for(let T=0;T<2;T++)h+=o((p+T+r)%r,(d+E+r)%r,(f+y+r)%r)*(T?u:1-u)*(E?M:1-M)*(y?v:1-v);return h};for(let n=0;n<t;n++)for(let i=0;i<t;i++)for(let l=0;l<t;l++){let r=64/t,p=l*r/8,d=i*r/8,f=n*r/8,g=Math.floor(p),u=Math.floor(d),M=Math.floor(f),v=3;for(let E=-1;E<=1;E++)for(let T=-1;T<=1;T++)for(let _=-1;_<=1;_++){let z=g+_,P=u+T,O=M+E,m=(z+8)%8,R=(P+8)%8,c=(O+8)%8,D=z+o(m,R,c)-p,U=P+o(m+31,R,c)-d,K=O+o(m,R+51,c)-f;v=Math.min(v,D*D+U*U+K*K)}let h=.62*a(l*r/16,i*r/16,n*r/16,4)+.28*a(l*r/8,i*r/8,n*r/8,8)+.1*a(l*r/4,i*r/4,n*r/4,16),y=((n*t+i)*t+l)*4;e[y]=Math.round(h*255),e[y+1]=Math.round((1-Math.min(1,Math.sqrt(v)))*255),e[y+2]=Math.round(a(l*r/2,i*r/2,n*r/2,32)*255),e[y+3]=255}let s=new A.Data3DTexture(e,t,t,t);return s.format=A.RGBAFormat,s.minFilter=s.magFilter=A.LinearFilter,s.wrapS=s.wrapT=s.wrapR=A.RepeatWrapping,s.unpackAlignment=1,s.needsUpdate=!0,s}function Fo(t,e={}){if(!t?.isWebGLRenderer||e.safe)return null;let o=e.cloudSize||512,a=e.cloudSteps||24,s=e.cloudInterval||250,n=Oa(e.noiseSize||64),i=new A.WebGLRenderTarget(o,o/2,{type:t.extensions.has("EXT_color_buffer_float")?A.HalfFloatType:A.UnsignedByteType,depthBuffer:!1,stencilBuffer:!1});i.texture.wrapS=A.RepeatWrapping;let l=[i,i.clone(),i.clone()],r=0,p=0,d="",f,g="",u=.5,M=.5,v=[new A.Vector2(1,0),new A.Vector2(-1,0)],h={seedOffset:{value:new A.Vector2},sunriseBearing:{value:v[0]},sunsetBearing:{value:v[1]},coverageThreshold:{value:.5},distantThreshold:{value:.5},marchSteps:{value:a},origin:{value:new A.Vector3(0,.015,0)},volume:{value:n},coverage:{value:0},sun:{value:new A.Vector3(0,1,0)},sunTint:{value:new A.Color("white")},day:{value:1},storm:{value:0},offset:{value:new A.Vector2}},y=new A.ShaderMaterial({glslVersion:A.GLSL3,uniforms:h,depthTest:!1,depthWrite:!1,vertexShader:"out vec2 cloudUV;void main(){cloudUV=uv;gl_Position=vec4(position.xy,0.,1.);}",fragmentShader:`
 precision highp float;precision highp sampler3D;in vec2 cloudUV;out vec4 cloudResult;
 uniform sampler3D volume;uniform float marchSteps;uniform float coverageThreshold,distantThreshold,coverage,day,storm;uniform vec3 sun,sunTint,origin;uniform vec2 offset,seedOffset,sunriseBearing,sunsetBearing;
 float topDistance(vec3 d,float height){float r=6360.+origin.y,b=r*d.y;return -b+sqrt(max(0.,b*b+pow(6360.+height,2.)-r*r));}
 float regionalHash(vec2 p){vec3 q=fract(vec3(p.xyx)*.1031);q+=dot(q,q.yzx+33.33);return fract((q.x+q.y)*q.z);}
 float regionalNoise(vec2 p){vec2 c=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(regionalHash(c),regionalHash(c+vec2(1,0)),f.x),mix(regionalHash(c+vec2(0,1)),regionalHash(c+vec2(1,1)),f.x),f.y);}
 float density(vec3 p,bool detailed){
  vec2 ground=p.xz-offset-seedOffset;
  vec2 warped=ground+vec2(regionalNoise(ground*.031),regionalNoise(ground*.027+19.))*8.;
  float region=.68*regionalNoise(warped*.065)+.32*regionalNoise(warped*.151+37.);
  // Regional coverage, independent of local erosion: clear corridors between cloud banks.
  float distanceWeight=smoothstep(20.,60.,length(p.xz-origin.xz));
  float localThreshold=mix(coverageThreshold,distantThreshold,distanceWeight);
  float mask=smoothstep(localThreshold-.035,localThreshold+.035,region);
  float type=regionalNoise(ground*.09+71.);
  float altitude=length(p+vec3(0.,6360.,0.))-6360.;
  // Kilometre-scale rounded billows disturb both boundaries, not a flat slab.
  float billow=regionalNoise(warped*.65+13.);
  float base=1.32+.24*type+.18*(billow-.5);
  float thickness=.75+.90*type+.40*billow;
  float h=(altitude-base)/thickness;if(h<=0.||h>=1.||mask<.001)return 0.;
  vec3 uv=vec3(warped.x*.12,h*.52,warped.y*.12);
  vec3 n=texture(volume,uv).rgb;
  float shape=n.r*.52+n.g*.48;
  float detail=texture(volume,uv*3.7+vec3(.13,.21,.07)).g;
  float profile=pow(max(0.,4.*h*(1.-h)),.65);
  float body=max(0.,shape-mix(.48,.32,coverage))*5.5;
  body=max(0.,body-(1.-detail)*mix(.10,.22,type));
  return body*profile*mask*smoothstep(0.,.06,coverage);
 }
 void main(){if(coverage<.0001||origin.y>=3.8){cloudResult=vec4(0.);return;}float az=(cloudUV.x-.5)*6.2831853,elevation=cloudUV.y*cloudUV.y*1.5707963;vec3 d=vec3(cos(az)*cos(elevation),sin(elevation),sin(az)*cos(elevation));float start=origin.y>=1.2?0.:max(0.,topDistance(d,1.2)),end=min(topDistance(d,3.8),start+35.);float stepSize=(end-start)/marchSteps;float jitter=fract(sin(dot(gl_FragCoord.xy,vec2(12.9898,78.233)))*43758.5453);vec3 color=vec3(0.);float transmittance=1.;float mu=dot(d,sun),forward=.10+.055*(1.-.65*.65)/pow(max(.04,1.+.65*.65-2.*.65*mu),1.5);
 for(int i=0;i<48;i++){if(float(i)>=marchSteps)break;vec3 p=origin+d*(start+(float(i)+.2+.6*jitter)*stepSize);float rho=density(p,true);if(rho>.001){float optical=0.;for(int j=0;j<2;j++){float dist=.25+float(j)*.60;optical+=density(p+sun*dist,false)*.60;}float shadow=exp(-optical*5.);float a=1.-exp(-rho*stepSize*4.2);float h=clamp((length(p+vec3(0.,6360.,0.))-6360.-1.3)/1.8,0.,1.);vec3 ambient=mix(vec3(.19,.25,.33),vec3(.52,.60,.69),h)*(.008+.992*day)*(1.-storm*.38);vec3 direct=sunTint*shadow*(.65+forward)*day*(1.-storm*.55);color+=transmittance*a*(ambient+direct);transmittance*=1.-a;if(transmittance<.015)break;}}
 // Distance haze changes radiance, not optical coverage: distant thick clouds still occlude the sun.
 float distanceFade=exp(-start*.025);vec3 aerialTint=vec3(.52,.60,.69)*(.008+.992*day);cloudResult=vec4(mix(aerialTint*(1.-transmittance),color,distanceFade),1.-transmittance);}`}),E=new A.Scene,T=new A.Mesh(new A.PlaneGeometry(2,2),y),_=new A.Camera;E.add(T);let z=e.mobile?8:16,P="",O=-1/0,m=null;function R(b){b.cloudSeedOffset&&h.seedOffset.value.copy(b.cloudSeedOffset.value),h.origin.value.copy(b.cloudOrigin.value),h.coverage.value=b.cloud.value,h.coverageThreshold.value=u,h.distantThreshold.value=M,h.sun.value.copy(b.sunPosition.value),h.sunTint.value.copy(b.sunColor.value),h.day.value=b.day.value,h.storm.value=b.storm.value,h.offset.value.copy(b.cloudOffset.value)}function c(b,B,N){let $=Math.floor(B*o/2/N),ie=Math.floor((B+1)*o/2/N);b.scissor.set(0,$,o,ie-$),b.scissorTest=!0;let Oe=t.getRenderTarget(),Be=t.autoClear;try{t.autoClear=!0,t.setRenderTarget(b),t.render(E,_)}finally{t.setRenderTarget(Oe),t.autoClear=Be}}let D=!1,U=s;function K(b,B,N,$){let ie=r;p=ie,r=N,O=B,U=s,D=!0,b.cloudMap.value=l[r].texture,b.cloudMapPrevious.value=l[$?r:ie].texture,b.cloudBlend.value=$?1:0}let k;return{tileCount:z,prepare(b=()=>Promise.resolve()){return k??=(async()=>{await b(),t.initTexture(n),await b(),await t.compileAsync?.(E,_);for(let B of l)await b(),t.initRenderTarget(B),await new Promise(N=>setTimeout(N,0))})()},setQuality(b){let B=It[b]||It.medium;o===B.size&&a===B.steps||(o=B.size,a=B.steps,s=B.interval,h.marchSteps.value=a,P="",m=null)},get texture(){return l[r].texture},update(b,B=performance.now()){if(b.cloud.value<1e-4){m=null,P="",b.useVolumeClouds.value=0;return}if(b.useVolumeClouds.value=1,b.cloudBlend.value=Math.min(1,(B-O)/U),m){m.tile<z&&c(l[m.target],m.tile++,z),m.tile===z&&(!D||B-O>=U)&&(P=m.key,K(b,B,m.target,!D),m=null);return}let N=[b.sunriseBearing?.value||v[0],b.sunsetBearing?.value||v[1]],$=b.cloudSeedOffset?.value?.toArray()||[0,0],ie=N.map(we=>we.toArray().join(",")).join(";")+":"+$.join(",");ie!==d&&(v.forEach((we,Fe)=>we.copy(N[Fe])),f=Oo(v.map(we=>we.toArray()),$),d=ie,g="");let Oe=d+":"+b.cloud.value.toFixed(2);Oe!==g&&(u=Gt(f,b.cloud.value),M=Gt(f,Bo(b.cloud.value)),g=Oe);let Be=[d,b.cloud.value,b.day.value,b.storm.value,...b.sunPosition.value.toArray(),...b.cloudOffset.value.toArray(),...b.cloudOrigin.value.toArray()].join(",");if(Be===P)return;R(b);let lt=l.findIndex((we,Fe)=>Fe!==r&&Fe!==p);l[lt].setSize(o,o/2),m={key:Be,target:lt,tile:1},c(l[lt],0,z)},dispose(){n.dispose(),l.forEach(b=>b.dispose()),T.geometry.dispose(),y.dispose()}}}import*as W from"../3d/vendor/three.module.js";function Go(t,e={}){if(!t?.isWebGLRenderer||e.safe||!t.extensions.has("EXT_color_buffer_float"))return null;let o=e.atmosphereSize||256,a=e.atmosphereInterval||250,s=new W.WebGLRenderTarget(o,o/2,{type:W.HalfFloatType,depthBuffer:!1,stencilBuffer:!1});s.texture.wrapS=W.RepeatWrapping;let n={sun:{value:new W.Vector3(1,1,0).normalize()},aerosol:{value:1}},i=new W.ShaderMaterial({uniforms:n,depthTest:!1,depthWrite:!1,vertexShader:"varying vec2 uvSky;void main(){uvSky=uv;gl_Position=vec4(position.xy,0.,1.);}",fragmentShader:`
 precision highp float;varying vec2 uvSky;uniform vec3 sun;uniform float aerosol;
 const float R=6360.,TOP=6460.,PI=3.14159265359;
 const vec3 betaR=vec3(.005802,.013558,.033100),ozone=vec3(.000650,.001881,.000085);
 float exitDistance(vec3 p,vec3 d,float r){float b=dot(p,d);return -b+sqrt(max(0.,b*b-dot(p,p)+r*r));}
 vec3 density(vec3 p){float h=max(0.,length(p)-R);return vec3(exp(-h/8.),exp(-h/1.2),max(0.,1.-abs(h-25.)/15.));}
 vec3 extinction(vec3 od){return betaR*od.x+vec3(.00444*aerosol)*od.y+ozone*od.z;}
 vec3 solarTransmission(vec3 p){float b=dot(p,sun),disc=b*b-dot(p,p)+R*R;if(b<0.&&disc>0.)return vec3(0.);float length=exitDistance(p,sun,TOP);vec3 od=vec3(0.);for(int j=0;j<8;j++){float a=float(j)/8.,b=float(j+1)/8.;float t0=length*a*a,t1=length*b*b;od+=density(p+sun*((t0+t1)*.5))*(t1-t0);}return exp(-extinction(od));}
 void main(){float az=(uvSky.x-.5)*2.*PI;float elevation=uvSky.y*uvSky.y*PI*.5;vec3 d=vec3(cos(az)*cos(elevation),sin(elevation),sin(az)*cos(elevation));vec3 origin=vec3(0.,R+.015,0.);float distance=exitDistance(origin,d,TOP);vec3 optical=vec3(0.),radiance=vec3(0.);float mu=dot(d,sun),phaseR=3./(16.*PI)*(1.+mu*mu),g=.8;float phaseM=3./(8.*PI)*(1.-g*g)*(1.+mu*mu)/((2.+g*g)*pow(max(.001,1.+g*g-2.*g*mu),1.5));
 for(int i=0;i<24;i++){float a=float(i)/24.,b=float(i+1)/24.;float t0=distance*a*a,t1=distance*b*b,stepLength=t1-t0;vec3 p=origin+d*((t0+t1)*.5),rho=density(p),segment=rho*stepLength;vec3 transmit=exp(-extinction(optical+segment*.5))*solarTransmission(p);radiance+=transmit*(betaR*rho.x*phaseR+vec3(.003996*aerosol)*rho.y*phaseM)*stepLength;optical+=segment;}
 gl_FragColor=vec4(radiance*8.,1.);}`}),l=new W.Scene,r=new W.Mesh(new W.PlaneGeometry(2,2),i),p=new W.Camera;l.add(r);let d=[s,s.clone()],f=0,g=0,u=1,M="",v=-1/0;return{get texture(){return d[f].texture},get previousTexture(){return d[g].texture},get blend(){return u},update(h,y,E=performance.now()){let T=Math.max(0,Math.min(1,(E-v)/a));u=T*T*(3-2*T);let _=[h.x,h.y,h.z,y].join(",");if(_===M||E-v<a)return;let z=!M,P=1-f;n.sun.value.copy(h).normalize(),n.aerosol.value=.12+y*2;let O=t.getRenderTarget(),m=t.autoClear;try{t.autoClear=!0,t.setRenderTarget(d[P]),t.render(l,p)}finally{t.setRenderTarget(O),t.autoClear=m}g=z?P:f,f=P,u=z?1:0,M=_,v=E},dispose(){d.forEach(h=>h.dispose()),r.geometry.dispose(),i.dispose()}}}function No({panorama:t=!0,renderer:e,device:o={},probe:a=!1}={}){let s=new C.DataTexture(new Uint8Array([0,0,0,255]),1,1);s.needsUpdate=!0;let n=Go(a?null:e,o),i=Fo(a?null:e,o),l={cloudSeedOffset:{value:new C.Vector2},sunriseBearing:{value:new C.Vector2(1,0)},sunsetBearing:{value:new C.Vector2(-1,0)},nightStyle:{value:0},meteorEnabled:{value:1},starsEnabled:{value:1},cloudOrigin:{value:new C.Vector3(0,.015,0)},cloudBlend:{value:1},cloudMapPrevious:{value:i?.texture||s},cloudMap:{value:i?.texture||s},cloudOffset:{value:new C.Vector2},useVolumeClouds:{value:0},atmosphereBlend:{value:1},atmosphereMapPrevious:{value:n?.texture||s},atmosphereMap:{value:n?.texture||s},useAtmosphere:{value:0},seaHorizon:{value:0},seaColor:{value:new C.Color("#8dbbdf")},sunPosition:{value:new C.Vector3(1,.5,0)},sunColor:{value:new C.Color("#fff4df")},day:{value:1},warm:{value:0},direct:{value:1},cloud:{value:.12},storm:{value:0},twinkleTime:{value:0},clock:{value:0},radius:{value:.00465},showSun:{value:1},stars:{value:0},sidereal:{value:0},galaxyMap:{value:s},galaxyMix:{value:0}},r=new C.ShaderMaterial({side:C.BackSide,depthWrite:!1,uniforms:l,vertexShader:"varying vec3 ray;void main(){ray=position;vec4 p=projectionMatrix*mat4(mat3(viewMatrix))*modelMatrix*vec4(position,1.0);gl_Position=p.xyww;}",fragmentShader:`
 uniform sampler2D cloudMap,cloudMapPrevious;uniform float cloudBlend;uniform float useVolumeClouds;uniform vec2 cloudOffset;uniform sampler2D atmosphereMap;uniform float useAtmosphere;uniform sampler2D galaxyMap;uniform float galaxyMix;
 precision highp float;uniform sampler2D atmosphereMapPrevious;uniform float atmosphereBlend;varying vec3 ray;uniform vec3 sunPosition,sunColor,seaColor;uniform float starsEnabled,nightStyle,meteorEnabled;uniform float seaHorizon;uniform float day,warm,direct,cloud,storm,clock,radius,showSun,stars,sidereal,twinkleTime;
 ${Do}
 float hash(vec2 p){vec3 p3=fract(vec3(p.xyx)*.1031);p3+=dot(p3,p3.yzx+33.33);return fract((p3.x+p3.y)*p3.z);}
 float noise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.0-2.0*f);return mix(mix(hash(i),hash(i+vec2(1,0)),f.x),mix(hash(i+vec2(0,1)),hash(i+vec2(1,1)),f.x),f.y);}
 float fbm(vec2 p){float v=0.,a=.55;for(int i=0;i<4;i++){v+=a*noise(p);p=p*2.03+17.3;a*=.48;}return v;}
 // Fixed celestial coordinates: stars never re-randomize when time or weather changes.
 vec3 celestial(vec3 d){float a=sidereal,c=cos(a),s=sin(a);vec3 pole=normalize(vec3(0.,.518,-.855));return d*c+cross(pole,d)*s+pole*dot(pole,d)*(1.-c);}
 // An all-sky photographic field resolves the bulge, rifts, nebulae and stellar density.
 // This fixed orientation is an artistic sky, not a date-calibrated planetarium.
 vec3 nightStars(vec3 direction){vec3 d=celestial(direction);vec3 pole=normalize(vec3(.76,-.58,.30));vec3 axis=normalize(vec3(.30,0.,-.76));vec3 other=cross(pole,axis);vec3 g=vec3(dot(d,axis),dot(d,other),dot(d,pole));vec2 uv=vec2(.5+atan(g.y,g.x)/6.28318530718,.5+asin(clamp(g.z,-1.,1.))/3.14159265359);// Separate the broad galactic field from unresolved photographic star grain.
 // Star-removed diffuse panorama; photographic bloom is never used as a point source.
 vec3 diffuse=texture2D(galaxyMap,uv).rgb;
 float haze=dot(diffuse,vec3(.2126,.7152,.0722));
 vec3 band=mix(vec3(haze),diffuse,mix(.65,1.15,nightStyle))*(mix(.68,1.8,nightStyle)/(1.+2.5*haze));
 vec2 grid=uv*vec2(160.,80.),cell=floor(grid);
 float latitude=cos((uv.y-.5)*3.14159265);
 vec2 metric=vec2(max(.025,latitude),1.);
 // Differentiate the continuous 3D direction, never wrapped longitude UVs.
 // Across the +/-pi seam, UV derivatives jump by a whole texture width.
 float pixel=max(length(fwidth(d))*.7071*(80./3.14159265),.0001);
 vec3 points=vec3(0.);
 for(int j=-1;j<=1;j++)for(int i=-1;i<=1;i++){
  vec2 neighbor=cell+vec2(float(i),float(j));
  vec2 key=vec2(mod(neighbor.x+160.,160.),neighbor.y);
  float seed=hash(key+13.7);
  if(seed>1.-.095*max(0.,latitude)&&neighbor.y>=0.&&neighbor.y<80.){
   vec2 center=neighbor+.16+.68*vec2(hash(key+37.1),hash(key+91.3));
   float distance=length((grid-center)*metric)/pixel;
   float magnitude=hash(key+51.9);
   // Gaussian pixel footprint: brightness varies, but stars never become resolved disks.
   float sigma=mix(.40,.60,pow(magnitude,4.));
   float core=exp(-.5*pow(distance/sigma,2.));
   float halo=exp(-.5*pow(distance/1.15,2.))*.025*pow(magnitude,6.);
   float phase=hash(key+77.)*6.2831853;
   float shimmer=1.+(.035+.045*(1.-max(direction.y,0.)))*(sin(twinkleTime*1.8+phase)+.25*sin(twinkleTime*3.1+phase*2.3));
   vec3 tint=mix(vec3(.78,.86,1.),vec3(1.,.90,.76),hash(key+19.));
   points+=tint*(core+halo)*mix(.045,.65,pow(magnitude,3.))*shimmer;
  }
 }
 float transmission=exp(-.10/max(.07,direction.y));
 return (band*galaxyMix+points)*transmission;}

 // Rare deterministic meteors: a short tapered trail, never a repeating shower.
 vec3 meteor(vec3 d,float pixel){
 float event=floor(twinkleTime/31.),age=mod(twinkleTime,31.)-4.-hash(vec2(event,7.))*12.;
 if(age<0.||age>1.5||meteorEnabled<.5)return vec3(0.);
 float az=hash(vec2(event,3.))*6.28318;
 vec3 start=normalize(vec3(cos(az),.8+hash(vec2(event,5.)),sin(az)));
 vec3 raw=cross(start,vec3(0.,1.,0.))*.8+vec3(0.,-.6,0.);
 vec3 tangent=normalize(raw-start*dot(raw,start)),plane=normalize(cross(start,tangent));
 float t=age/1.5,head=t*.30,along=atan(dot(d,tangent),dot(d,start));
 float across=asin(clamp(dot(d,plane),-1.,1.)),behind=head-along;
 float lengthTrail=min(.065,head),width=max(pixel*.55,.000035);
 float taper=clamp(1.-behind/max(lengthTrail,.00001),0.,1.);
 float trail=exp(-.5*pow(across/(width*(.35+.65*taper)),2.))*taper*taper;
 trail*=smoothstep(-width,width,behind)*(1.-smoothstep(lengthTrail-width,lengthTrail+width,behind));
 float core=exp(-.5*(across*across+behind*behind)/(width*width));
 float fade=smoothstep(0.,.12,t)*(1.-smoothstep(.65,1.,t));
 return vec3(.55,.65,.8)*(trail*.65+core)*fade;
 }
 void main(){vec3 d=normalize(ray);float angularPixel=max(length(dFdx(d)),length(dFdy(d)));float y=max(d.y,0.0),horizon=pow(1.0-y,5.0);vec3 zenith=vec3(.014,.12,.43),edge=vec3(.32,.54,.80);vec3 clear=mix(zenith,edge,exp(-5.0*y));float facing=pow(max(dot(normalize(vec3(d.x,.001,d.z)),normalize(vec3(sunPosition.x,.001,sunPosition.z))),0.0),5.0);clear=mix(clear,vec3(.94,.32,.105),warm*horizon*facing*.78);vec3 night=mix(vec3(.0015,.003,.012),vec3(.006,.013,.027),horizon);vec2 skyUV=vec2(.5+atan(d.z,d.x)/6.28318530718,sqrt(clamp(asin(clamp(d.y,0.,1.))/1.57079632679,0.,1.)));vec3 physical=mix(texture2D(atmosphereMapPrevious,skyUV).rgb,texture2D(atmosphereMap,skyUV).rgb,atmosphereBlend);vec3 color=mix(mix(night,clear,day),night*(1.-day)+physical,useAtmosphere);color=mix(color,vec3(.33,.39,.47)*(.025+.975*day),cloud*storm*.68);
 if(stars*starsEnabled>.0001)color+=(nightStars(d)+meteor(d,angularPixel))*stars*smoothstep(0.0,.18,d.y)*(1.-storm*.96);
 // Trace an apparent viewing ray back through the refracting atmosphere.
 vec3 solarRay=d;if(dot(d,normalize(sunPosition))>.97)solarRay=unrefractSunRay(d);
 // atan(cross,dot) remains stable at the disk centre; acos loses precision there.
 float angle=atan(length(cross(solarRay,normalize(sunPosition))),dot(solarRay,normalize(sunPosition)));float edgeAA=max(fwidth(angle),radius*mix(.10,.24,warm));float disk=1.0-smoothstep(radius-edgeAA,radius+edgeAA,angle);float limb=sqrt(max(0.0,1.0-pow(angle/radius,2.0)));float horizonAA=max(fwidth(d.y),.000001);float aboveSea=smoothstep(-horizonAA,horizonAA,d.y);
 // Only the part actually below the sea horizon is occulted, in world-ray coordinates.
 // Once the full refracted disk clears the horizon no camera-dependent crop is applied.
 float solar=showSun*aboveSea;
 // Sun-local scattering/exposure halo: smooth angular falloff, no full-scene bloom.
 float innerHalo=exp(-pow(angle/(radius*2.4),2.));
 float outerHalo=exp(-pow(angle/(radius*7.5),2.));
 vec3 haloTint=mix(sunColor,vec3(1.,.30,.045),warm*.7);
 vec4 cloudLight=mix(texture2D(cloudMapPrevious,skyUV),texture2D(cloudMap,skyUV),cloudBlend);
 float cloudOpacity=clamp(cloudLight.a*useVolumeClouds,0.,1.);
 float transmission=1.-cloudOpacity;
 // Cloud optical thickness controls the sun, without a low-altitude brightness override.
 float solarTransmission=transmission;
 // Cloud alpha already integrates Beer-Lambert extinction; do not apply it twice.
 float diskTransmission=transmission;
 color=color*transmission+cloudLight.rgb*useVolumeClouds;
 color+=solar*(sunColor*disk*(4.5+1.5*limb)*diskTransmission
   +(sunColor*innerHalo*.8+haloTint*outerHalo*mix(.07,.26,warm))*solarTransmission);

 // The distant ocean meets the same horizontal ray used to clip the solar disk.
 // Below the horizon the same grazing sky radiance continues behind the finite ocean.
 // Never insert a fixed fog-colour strip here.
 // Continue the distant sea beyond the finite water mesh, retaining sea/sky contrast.
 // A narrow angular marine haze band, independent of framebuffer resolution.
 float horizonSoftness=max(fwidth(d.y)*2.,.006);
 float seaSide=1.-smoothstep(-horizonSoftness,horizonSoftness,d.y);
 color*=mix(vec3(1.),mix(vec3(.90,.94,.96),vec3(.97),storm),seaSide);
 gl_FragColor=vec4(max(color,vec3(0.0)),1.0);#include <tonemapping_fragment>
 #include <colorspace_fragment>
 }`.replace(";#include",`;
#include`)}),p=!1,d=0,f;t&&typeof window<"u"&&typeof Image<"u"&&At(()=>new Promise(h=>{if(p){h();return}f=new C.TextureLoader().load(new URL("./assets/sky/galaxy-diffuse.jpg",import.meta.url).href,y=>{if(p){y.dispose(),h();return}y.colorSpace=C.SRGBColorSpace,y.wrapS=C.RepeatWrapping,y.minFilter=C.LinearMipmapLinearFilter,y.magFilter=C.LinearFilter,y.anisotropy=4,l.galaxyMap.value=y,d=performance.now(),h()},void 0,h)})),r.addEventListener("dispose",()=>{p=!0,n?.dispose(),i?.dispose(),s.dispose(),f?.dispose()});let g=new C.Mesh(new C.SphereGeometry(1,48,24),r);g.onBeforeRender=(h,y,E)=>{l.cloudOrigin.value.copy(E.position).multiplyScalar(.001),l.cloudOrigin.value.y=Math.max(.001,l.cloudOrigin.value.y),l.twinkleTime.value=performance.now()/1e3,d&&(l.galaxyMix.value=1-Math.exp(-(performance.now()-d)/1200))};let u=!o.startup,M=0,v=!0;return g.userData.setResourceWorkAllowed=h=>{v=!!h},g.userData.prepareClouds=async(h=()=>{},y=()=>Promise.resolve(),E="low")=>{if(!i||E==="off"){h(1);return}await i.prepare(y),i.setQuality(E);for(let T=0;T<i.tileCount;T++)await y(),i.update(l),h((T+1)/i.tileCount),await new Promise(_=>setTimeout(_,16));l.useVolumeClouds.value=M},g.userData.beginArrivalFade=()=>{M=0,l.useVolumeClouds.value=0},g.userData.setCloudQuality=h=>{u=h!=="off",u&&i?.setQuality(h)},g.userData.updateAtmosphere=(h=0)=>{o.isRenderActive?.()!==!1&&(v&&n?.update(l.sunPosition.value,l.cloud.value),n&&(l.atmosphereMap.value=n.texture,l.atmosphereMapPrevious.value=n.previousTexture,l.atmosphereBlend.value=n.blend),l.useAtmosphere.value=Ye(l.useAtmosphere.value,n?1:0,h),u&&v&&i?.update(l),M=Ye(M,u&&i&&l.cloud.value>=1e-4?1:0,h),l.useVolumeClouds.value=M)},g.name="Continuous Shanghai sky",g.frustumCulled=!1,g.scale.setScalar(1e4),g}var ge=(t,e,o)=>{let a=Math.max(0,Math.min(1,(o-t)/(e-t)));return a*a*(3-2*a)};function rt(t,e=new Date){let o=new Date(+e+288e5),a=o.getUTCFullYear(),s=Date.UTC(a,0,1),n=Math.floor((Date.UTC(a,o.getUTCMonth(),o.getUTCDate())-s)/864e5)+1,i=(Date.UTC(a+1,0,1)-s)/864e5,l=(t%24+24)%24,r=2*Math.PI/i*(n-1+(l-12)/24),p=229.18*(75e-6+.001868*Math.cos(r)-.032077*Math.sin(r)-.014615*Math.cos(2*r)-.040849*Math.sin(2*r)),d=.006918-.399912*Math.cos(r)+.070257*Math.sin(r)-.006758*Math.cos(2*r)+907e-6*Math.sin(2*r)-.002697*Math.cos(3*r)+.00148*Math.sin(3*r),f=31.2304*Math.PI/180,g=(l*60+p+4*121.4737-480-720)*Math.PI/720,u=-Math.cos(d)*Math.sin(g),M=Math.sin(f)*Math.sin(d)+Math.cos(f)*Math.cos(d)*Math.cos(g),v=Math.sin(f)*Math.cos(d)*Math.cos(g)-Math.cos(f)*Math.sin(d),h=Math.asin(Math.max(-1,Math.min(1,M)))*180/Math.PI,y=ge(-6,12,h),E=ge(-.8,3,h),T=1-ge(0,20,h);return{direction:[u,M,v],elevation:h,daylight:y,direct:E,warm:T,night:1-ge(-9,-2,h),physicalRadius:.00465*(1+.0167*Math.cos(r)),radius:.00465*(1+.0167*Math.cos(r)),solarNoon:(720-4*121.4737-p+480)/60}}function Wo(t=new Date){let e=(o,a,s)=>{for(let n=0;n<30;n++){let i=(o+a)/2;rt(i,t).elevation>-.833===s?a=i:o=i}return(o+a)/2};return{sunrise:e(0,12,!0),sunset:e(12,24,!1)}}var Ie=[ne.origin[0]/w,ne.origin[2]/w,(ne.halfWidth+8)/w,(ne.halfDepth+8)/w];var Re=t=>Number(t).toFixed(9),Uo=`float terraceDistance(vec2 p){vec2 q=abs(p-vec2(39.,0.))-vec2(15.,16.5);return length(max(q,vec2(0.)))+min(max(q.x,q.y),0.);}
float coastHash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
float coastNoise(vec2 p){vec2 i=floor(p),f=fract(p);f=f*f*(3.-2.*f);return mix(mix(coastHash(i),coastHash(i+vec2(1,0)),f.x),mix(coastHash(i+vec2(0,1)),coastHash(i+vec2(1,1)),f.x),f.y);}
float beachWidth(vec2 p){return 10.+8.*smoothstep(30.,54.,p.x)+4.*smoothstep(-10.,20.,p.y)+10.*(coastNoise(p*.12)-.5)+5.*(coastNoise(p*.31+vec2(4,-3))-.5)+1.*(coastNoise(p*.41)-.5);}
float beachMask(vec2 p){float d=terraceDistance(p),w=beachWidth(p);float sides=1.-(1.-smoothstep(48.,54.,p.x)*smoothstep(-25.,-20.,p.y))*(1.-smoothstep(10.5,16.5,p.y)*smoothstep(24.,32.,p.x))*(1.-smoothstep(46.,53.,p.x)*(1.-smoothstep(-17.,-12.,p.y)));return sides*smoothstep(-1.2,-.15,d)*(1.-smoothstep(w*.3,w*1.8,d));}
float beachDepth(vec2 p){float w=beachWidth(p),d=max(0.,terraceDistance(p))*17./w;return -${Re(.65*w)}+2.25*smoothstep(0.,13.,d)+.18*(coastNoise(p*1.1)-.5)*smoothstep(.5,2.,d)*(1.-smoothstep(5.,9.,d));}
float baseSeaDepthAt(vec2 p){
 float campus=length(max(abs(p+vec2(20.5,6.0))-vec2(74.5,49.0),vec2(0.0)));
 float residence=(length((p-vec2(${Re(Ie[0])},${Re(Ie[1])}))/vec2(${Re(Ie[2])},${Re(Ie[3])}))-1.0)*${Re(Ie[3])};
 float distance=max(0.0,min(campus,residence));
 float shallows=1.5+.7*(.5+.5*sin(p.x*.047+p.y*.029))+.8*smoothstep(0.0,22.0,distance);
 float depth=mix(mix(shallows,88.0,smoothstep(22.0,205.0,distance)),beachDepth(p),beachMask(p));return depth;
}
float seaDepthAt(vec2 p){return baseSeaDepthAt(p);}
`;import*as Ve from"../3d/vendor/three.module.js";import*as G from"../3d/vendor/three.module.js";var jn=new G.Vector3(0,1,0);import*as Ae from"../3d/vendor/three.module.js";import*as de from"../3d/vendor/three.module.js";import*as nt from"../3d/vendor/three.module.js";var si={position:[-69,13,29].map(t=>t*w),target:[-84,5.3,8].map(t=>t*w)};import*as ye from"../3d/vendor/three.module.js";import*as X from"../3d/vendor/three.module.js";var it=2*Z+3.2/w+.2+1.5/w,jo=[{number:1,name:"\u62A5\u544A\u5385",shot:"\u62A5\u544A\u5385",roof:"Upper seminar lounge",rooms:[{name:"\u4E00\u5C42 \xB7 \u62A5\u544A\u5385",shot:"\u62A5\u544A\u5385",room:0},{name:"\u4E8C\u5C42 \xB7 \u5BA2\u5385",shot:"\u4E8C\u697C\u5BA2\u5385"}]},{number:2,name:"\u6559\u5B66\u697C",shot:"\u6559\u5B66\u697C",rooms:[{name:"\u4E00\u5C42 \xB7 KM \u7814\u8BFB\u6559\u5BA4",room:1},{name:"\u4E8C\u5C42 \xB7 \u6559\u5BA4",room:2},{name:"\u4E09\u5C42 \xB7 \u6559\u5BA4",room:3}]},{number:3,name:"\u56FE\u4E66\u9986",shot:"\u4E66\u5BA4",roof:"Independent quiet library",rooms:[{name:"\u9605\u89C8\u5BA4",shot:"\u4E66\u5BA4"}]},{number:4,name:"\u5B66\u672F\u5BA2\u5385",shot:"\u5B66\u672F\u5BA2\u5385",roof:"Upper private studies",rooms:[{name:"\u4E00\u5C42 \xB7 \u5BA2\u5385",shot:"\u5B66\u672F\u5BA2\u5385"},{name:"\u4E8C\u5C42 \xB7 \u4E66\u623F",shot:"\u697C\u4E0A\u4E66\u623F"}]},{number:5,name:"\u8BA8\u8BBA\u697C",shot:"\u8BA8\u8BBA\u697C",roof:"Upper small seminar",rooms:[{name:"\u4E00\u5C42 \xB7 \u8BA8\u8BBA\u5BA4",shot:"\u8BA8\u8BBA\u697C"},{name:"\u4E8C\u5C42 \xB7 \u5C0F\u8BA8\u8BBA\u5BA4",shot:"\u697C\u4E0A\u8BA8\u8BBA\u5BA4"}]},{number:6,name:"\u5496\u5561\u5C4B",shot:"\u5496\u5561\u5C4B",roof:"North coffee cabin",rooms:[{name:"\u5496\u5561\u5BA4",shot:"\u5496\u5561\u5C4B"}]},{number:7,name:"\u8336\u5BA4",shot:"\u8336\u5BA4",roof:"Service and tea kitchen",rooms:[{name:"\u8336\u5BA4\u4E0E\u53A8\u623F",shot:"\u8336\u5BA4"}]},{number:8,name:"\u5BA2\u820D\u4E00",shot:"\u5BA2\u820D\u4E00",roof:"Quiet residential villa 1",rooms:[{name:"\u5BA2\u623F",shot:"\u5BA2\u820D\u4E00"}]},{number:9,name:"\u5BA2\u820D\u4E8C",shot:"\u5BA2\u820D\u4E8C",roof:"Quiet residential villa 2",rooms:[{name:"\u5BA2\u623F",shot:"\u5BA2\u820D\u4E8C"}]}];jo.push({number:10,name:"\u4F4F\u5B85",shot:"\u6D77\u4E0A\u4F4F\u5B85",rooms:zo});var fe=(t,e,o)=>({name:t,title:t,description:"\u81EA\u7531\u89C2\u5BDF \xB7 \u62D6\u52A8\u6539\u53D8\u89C6\u89D2",duration:25,fov:58,positions:[e,[...e]],targets:[o,[...o]]}),Wa=[fe("\u5B66\u672F\u5BA2\u5385",[-6,Z+1.6/w,2],[-6,1.2,-5]),fe("\u697C\u4E0A\u4E66\u623F",[-7,it,-3],[-7,it-.3,-8]),fe("\u8BA8\u8BBA\u697C",[11.5,Z+1.6/w,2],[11.5,1.2,-5]),fe("\u697C\u4E0A\u8BA8\u8BBA\u5BA4",[11,it,-3],[11,it-.3,-8]),fe("\u5496\u5561\u5C4B",[39,Z+1.6/w,-19.8],[39,1.2,-23]),fe("\u8336\u5BA4",[-32.5,Z+1.6/w,20],[-38,1.2,19]),fe("\u5BA2\u820D\u4E00",[-53.5,Z+1.6/w,-27],[-57,1.2,-28]),fe("\u5BA2\u820D\u4E8C",[-44.5,Z+1.6/w,-37],[-48,1.2,-38])];Wa.push(..._o);async function qo(t,e,o,a,s){let i=Pt("./assets/waternormals.jpg",{critical:!0,phase:"entry"});i.wrapS=i.wrapT=x.RepeatWrapping;let l={shoreMap:null},r=new x.ShaderMaterial({transparent:!0,depthWrite:!0,uniforms:x.UniformsUtils.merge([x.UniformsLib.fog,{oceanStudy:{value:0},oceanLite:{value:1},oceanCameraWorld:{value:new x.Matrix4},oceanInverseProjection:{value:new x.Matrix4},oceanProjection:{value:new x.Matrix4},oceanLevel:{value:2.55*w},windWaves:{value:1},waveStrength:{value:.5},reflectionDetail:{value:1},sunReflection:{value:1},windFlow:{value:new x.Vector2(1,0)},waveOffset:{value:new x.Vector2},windSpeed:{value:2},skyDay:{value:1},skyCoverage:{value:0},skyStorm:{value:0},waterDetail:{value:1},skyMap:{value:null},skyCloudMap:{value:null},skyCloudPrevious:{value:null},skyCloudBlend:{value:1},skyCloudEnabled:{value:0},skyPhysical:{value:0},solarRadius:{value:.00465},sunTint:{value:new x.Color("#fff4df")},sunStrength:{value:1},rainAmount:{value:0},overcast:{value:0},time:{value:0},nightVisibility:{value:1},siteScale:{value:w},normalMap:{value:i},shoreMap:{value:l.shoreMap},sunDirection:{value:new x.Vector3(1,.5,.4).normalize()}}]),fog:!0,vertexShader:`
      uniform mat4 oceanCameraWorld,oceanInverseProjection;
      varying vec3 oceanRay;
      void main(){
        vec4 viewRay=oceanInverseProjection*vec4(position.xy,1.,1.);
        oceanRay=mat3(oceanCameraWorld)*viewRay.xyz;
        gl_Position=vec4(position.xy,0.,1.);
      }`,fragmentShader:`
      uniform float windWaves,waveStrength,reflectionDetail,sunReflection;uniform vec2 windFlow,waveOffset;uniform float windSpeed,skyDay,skyCoverage,skyStorm;uniform sampler2D skyMap,skyCloudMap,skyCloudPrevious;uniform float skyPhysical,skyCloudBlend,skyCloudEnabled,solarRadius,waterDetail;uniform vec3 sunTint;uniform float sunStrength,overcast,rainAmount;uniform float time;uniform float nightVisibility;uniform float siteScale;uniform sampler2D normalMap;uniform sampler2D shoreMap;uniform vec3 sunDirection;uniform float oceanLevel;uniform mat4 oceanProjection;varying vec3 oceanRay;
      #include <common>
      #include <fog_pars_fragment>
      ${Uo}
      uniform float oceanStudy,oceanLite;
      float solarCloudTransmission(){
        vec3 d=normalize(sunDirection);
        vec2 uv=vec2(.5+atan(d.z,d.x)/6.2831853,sqrt(clamp(asin(clamp(d.y,0.,1.))/1.5707963,0.,1.)));
        float opacity=mix(texture2D(skyCloudPrevious,uv).a,texture2D(skyCloudMap,uv).a,skyCloudBlend);
        return clamp(1.-opacity*skyCloudEnabled,0.,1.);
      }
      vec2 waveHash(vec2 p){return fract(sin(vec2(dot(p,vec2(127.1,311.7)),dot(p,vec2(269.5,183.3))))*43758.5453);}
      vec3 scatteredNormal(vec2 p){
        vec2 cell=floor(p*.7),f=fract(p*.7);f=f*f*(3.-2.*f);
        vec2 dx=dFdx(p),dy=dFdy(p);
        vec3 n00=textureGrad(normalMap,p+waveHash(cell)*19.,dx,dy).xyz;
        vec3 n10=textureGrad(normalMap,p+waveHash(cell+vec2(1,0))*19.,dx,dy).xyz;
        vec3 n01=textureGrad(normalMap,p+waveHash(cell+vec2(0,1))*19.,dx,dy).xyz;
        vec3 n11=textureGrad(normalMap,p+waveHash(cell+vec2(1,1))*19.,dx,dy).xyz;
        return mix(mix(n00,n10,f.x),mix(n01,n11,f.x),f.y)*2.-1.;
      }
      // Analytic shallow-water height field. Gradients bend rays; Hessians focus them.
      void rippleField(vec2 p,out vec2 gradient,out mat2 curvature){
        gradient=vec2(0.);curvature=mat2(0.);
        for(int i=0;i<5;i++){
          float k=float(i),angle=.43+k*2.399963;
          vec2 direction=vec2(cos(angle),sin(angle));
          float frequency=2.4+k*.87,amplitude=.085/(1.+k*.32);
          vec2 crossDirection=vec2(-direction.y,direction.x);
          float warp=dot(p,crossDirection)*.47+time*.13+k*2.17;
          float phase=dot(p,direction)*frequency-time*sqrt(9.81*frequency)+k*1.37+.8*sin(warp);
          vec2 g=direction*frequency+crossDirection*(.376*cos(warp));
          gradient+=g*(amplitude*cos(phase));
          mat2 outerG=mat2(g.x*g.x,g.x*g.y,g.x*g.y,g.y*g.y);
          mat2 outerCross=mat2(crossDirection.x*crossDirection.x,crossDirection.x*crossDirection.y,crossDirection.x*crossDirection.y,crossDirection.y*crossDirection.y);
          curvature+=amplitude*(-sin(phase)*outerG-cos(phase)*.17672*sin(warp)*outerCross);
        }
      }
      float sandCaustic(vec2 bottom,float depth){
        vec2 p=bottom,gradient;mat2 curvature;float travel=min(depth,2.5)*.25;
        // Two bounded inverse-ray iterations estimate the water entry point for this sand point.
        for(int i=0;i<2;i++){rippleField(p,gradient,curvature);p=bottom-clamp(gradient*travel,vec2(-.35),vec2(.35));}
        rippleField(p,gradient,curvature);
        mat2 jacobian=mat2(1.)+curvature*travel;
        float area=abs(jacobian[0][0]*jacobian[1][1]-jacobian[0][1]*jacobian[1][0]);
        // Finite sun footprint prevents singular, razor-sharp or unbounded light lines.
        return 1.5*exp(-area*area/.025);
      }
      vec3 grazingSky(vec2 heading){
        vec2 hUV=vec2(.5+atan(heading.y,heading.x)/6.28318530718,0.);
        vec3 h=mix(vec3(.07,.24,.43)*nightVisibility,texture2D(skyMap,hUV).rgb+vec3(.006,.013,.027)*(1.-skyDay),skyPhysical);
        h=mix(h,vec3(.33,.39,.47)*(.025+.975*skyDay),skyCoverage*skyStorm*.68);
        vec4 c=mix(texture2D(skyCloudPrevious,hUV),texture2D(skyCloudMap,hUV),skyCloudBlend);
        return h*(1.-c.a*skyCloudEnabled)+c.rgb*skyCloudEnabled;
      }
      float shoreHeight(vec2 p){
        float d=seaDepthAt(p);
        float envelope=beachMask(p)*exp(-max(d,0.)*.65);
        float phase=time*.72+terraceDistance(p)*.38+coastNoise(p*.08)*1.5;
        return envelope*(.13*sin(phase)+.045*sin(phase*1.43+1.7));
      }
      void main(){
        vec3 rayDirection=normalize(oceanRay);
        if(rayDirection.y>=-.0000001||cameraPosition.y<=oceanLevel)discard;
        float travel=(oceanLevel-cameraPosition.y)/rayDirection.y;
        vec3 vWorld=cameraPosition+rayDirection*travel;
        // Lightweight sea retains depth, coastline, wind and sky colour, with
        // one normal sample and no surf transport, inverse rays or caustics.
        if(oceanLite>.5){
          vec2 uv=vWorld.xz/siteScale;
          float depth=seaDepthAt(uv);if(depth<=0.)discard;
          vec4 projected=oceanProjection*viewMatrix*vec4(vWorld,1.);
          gl_FragDepthEXT=min(.9999995,.5*projected.z/projected.w+.5);
          vec2 drift=waveOffset*windWaves;
          vec3 tex=texture2D(normalMap,uv*.035+vec2(time*.011,-time*.007)-drift*.007).xyz*2.-1.;
          vec3 normal=normalize(vec3(tex.x*.12,1.,tex.y*.12));
          vec3 view=normalize(cameraPosition-vWorld),reflected=reflect(-view,normal);
          reflected.y=max(.002,reflected.y);
          vec2 skyUV=vec2(.5+atan(reflected.z,reflected.x)/6.2831853,sqrt(clamp(asin(reflected.y)/1.5707963,0.,1.)));
          float fresnel=.0204+.9796*pow(1.-max(dot(normal,view),0.),5.);
          vec3 clarity=exp(-vec3(.42,.19,.12)*depth);
          vec3 body=(vec3(.54,.49,.36)*clarity+vec3(.008,.18,.23)*(1.-clarity))*nightVisibility;
          vec3 sky=mix(vec3(.07,.24,.43)*nightVisibility,texture2D(skyMap,skyUV).rgb,skyPhysical);
          vec3 color=mix(body,sky,fresnel);
          float glint=pow(max(dot(reflect(-sunDirection,normal),view),0.),96.);
          color+=sunTint*glint*.2*sunStrength*sunReflection*solarCloudTransmission();
          float fog=1.-exp(-fogDensity*fogDensity*travel*travel);
          color=mix(color,sky,fog);
          float alpha=(1.-beachMask(uv)*exp(-depth*3.2)*(1.-fresnel)*.88)*smoothstep(0.,.018,depth);
          gl_FragColor=vec4(color,alpha);
          #include <tonemapping_fragment>
          #include <colorspace_fragment>
          return;
        }
        // Solve the actual ray / displaced shallow-water surface intersection.
        // A bounded bracket avoids fixed-point divergence at grazing angles.
        vec2 flatUV=vWorld.xz/siteScale;
        if(oceanStudy>.5&&smoothstep(.01,.15,beachMask(flatUV))*(1.-smoothstep(1.4,3.4,seaDepthAt(flatUV)))>.98)discard;
        if(beachMask(flatUV)>.001&&seaDepthAt(flatUV)<4.){
          float lo=max(0.,(oceanLevel+.18-cameraPosition.y)/rayDirection.y);
          float hi=(oceanLevel-.18-cameraPosition.y)/rayDirection.y;
          for(int step=0;step<10;step++){
            float mid=(lo+hi)*.5;vec3 q=cameraPosition+rayDirection*mid;
            if(q.y>oceanLevel+shoreHeight(q.xz/siteScale))lo=mid;else hi=mid;
          }
          travel=(lo+hi)*.5;vWorld=cameraPosition+rayDirection*travel;
        }
        vec4 projected=oceanProjection*viewMatrix*vec4(vWorld,1.);
        gl_FragDepthEXT=min(.9999995,.5*projected.z/projected.w+.5);
        vec2 uv=vWorld.xz/siteScale;
        // Restore the earlier two counter-moving normal layers; their clocks are real-time.
        vec2 drift=waveOffset*windWaves;
        vec2 waveUV=uv*.035+vec2(time*.011,-time*.007)-drift*.007;
        vec2 bend=vec2(sin(uv.y*.023+sin(uv.x*.017)),sin(uv.x*.019+sin(uv.y*.013)))*.09;
        vec3 a=mix(texture2D(normalMap,waveUV+bend).xyz*2.-1.,scatteredNormal(waveUV+bend),.6);
        vec3 b=vec3(0.);if(waterDetail>.5)b=texture2D(normalMap,mat2(.7986,-.6018,.6018,.7986)*uv*.0173+vec2(-time*.008,time*.005)-drift*.005).xyz*2.-1.;
        float windGain=smoothstep(0.,14.,windSpeed)*windWaves;
        float effectiveWave=min(1.5,max(.5,waveStrength)+.8*windGain);
        float chop=mix(.20,.28,windGain)*effectiveWave;
        vec2 crossWind=vec2(-windFlow.y,windFlow.x);
        vec2 slopes=windFlow*(a.x+b.x)+crossWind*(a.y+b.y);
        slopes+=(windFlow*cos(dot(uv,windFlow)*.095-time*.61)
          +normalize(windFlow+crossWind*.73)*cos(dot(uv,windFlow+crossWind*.73)*.057-time*.43+1.7)*.57
          +normalize(windFlow-crossWind*.41)*cos(dot(uv,windFlow-crossWind*.41)*.137-time*.79+4.1)*.31)*.06*windGain;
        float surfaceDistance=length(vWorld.xz-cameraPosition.xz);
        float footprint=max(length(dFdx(uv)),length(dFdy(uv)));
        float detailFade=inversesqrt(1.+pow(surfaceDistance/650.,2.))*inversesqrt(1.+pow(footprint/.65,2.));
        vec2 rippleGradient;mat2 rippleCurvature;
        float beachInfluence=exp(-max(seaDepthAt(uv),0.)*.32);
        if(beachInfluence>.001){rippleField(vWorld.xz,rippleGradient,rippleCurvature);slopes=mix(slopes,-rippleGradient*.55/max(chop,.001),beachInfluence*.18);}
        vec3 normal=normalize(vec3(slopes.x*chop*detailFade,1.,slopes.y*chop*detailFade));
        // Expanding impact rings have staggered births and fade before cell edges.
        vec2 cell=floor(vWorld.xz*.65),local=fract(vWorld.xz*.65)-.5;
        float seed=fract(sin(dot(cell,vec2(127.1,311.7)))*43758.5453),age=fract(time*1.6+seed),r=length(local);
        float ring=exp(-pow((r-age*.42)/.025,2.))*(1.-age)*smoothstep(0.,.08,age)*(1.-smoothstep(.37,.48,r));
        normal=normalize(normal+vec3(local.x,0.,local.y)*ring*rainAmount*.22*detailFade);
        vec3 view=normalize(cameraPosition-vWorld);
        float nv=max(dot(normal,view),.001);
        float fresnel=.0204+.9796*pow(1.0-nv,5.0);
        vec3 halfVector=normalize(sunDirection+view);float nh=max(dot(normal,halfVector),0.0);
        // Gaussian wave slopes suppress GGX's long bright tails at the horizon.
        // The half-vector determines the required slope, so sun elevation and
        // observer height naturally move and reshape the specular footprint.
        float alpha=.035+.09*windGain*effectiveWave+solarRadius*.45+rainAmount*.025,a2=alpha*alpha;
        float nh2=max(nh*nh,.0001),slope2=(1.-nh2)/nh2;
        float distribution=exp(-slope2/a2)/(3.14159265*a2*nh2*nh2);
        float nl=max(dot(normal,sunDirection),0.0),k=alpha*.5;
        float visibility=nv/(nv*(1.-k)+k)*nl/(nl*(1.-k)+k);
        float sunF=.0204+.9796*pow(1.-max(dot(view,halfVector),0.),5.);
        // Bound radiance smoothly; avoid a flat clipped white column at grazing angles.
        float radiance=distribution*visibility*sunF/(4.*nv+.001);
        float glitter=.85*(1.-exp(-radiance*.32));
        float swell=.5+.5*sin(uv.x*.11+uv.y*.067+time*.65);
        float depth=seaDepthAt(uv)+(vWorld.y-oceanLevel);if(depth<=0.)discard;
        vec3 transmission=exp(-vec3(.23,.105,.065)*depth);
        vec3 waterColor=vec3(.006,.065,.12)*(1.0-transmission)+vec3(.25,.37,.28)*transmission;
        waterColor*=.94+swell*.06;
        // One depth-driven optical model across the shelf: no beach-mask colour seam.
        float sand=exp(-depth*.16);
        if(sand>.001){
          vec2 bottom=uv-normal.xz*depth*.35;
          vec3 clarity=exp(-vec3(.42,.19,.12)*depth);
          vec3 sandColor=vec3(.54,.49,.36);
          vec3 shallow=sandColor*clarity+vec3(.008,.29,.34)*(1.-clarity);
          float caustic=sandCaustic(bottom*siteScale,depth)*exp(-surfaceDistance/180.)/(1.+pow(footprint/.4,2.));
          shallow+=vec3(.20,.27,.23)*caustic*exp(-depth*.6)*sunStrength;
          waterColor=mix(waterColor,shallow,sand);
        }
        vec2 shoreUV=vec2((uv.x+150.0)/250.0,(uv.y+110.0)/220.0);
        float inPatch=step(0.0,shoreUV.x)*step(shoreUV.x,1.0)*step(0.0,shoreUV.y)*step(shoreUV.y,1.0);
        float shoreDistance=texture2D(shoreMap,clamp(shoreUV,0.0,1.0)).r*20.0;
        float nearShore=(1.0-smoothstep(.2,8.0,shoreDistance))*inPatch;
        waterColor=mix(waterColor,vec3(.06,.30,.27),nearShore*.16);
        float foam=pow(.5+.5*sin(shoreDistance*2.2-time*.9+a.x*.7),8.0)*exp(-shoreDistance*.58)*nearShore;
        float wash=pow(max(0.,sin(depth*10.-time*.55+sin(uv.x*.21+uv.y*.13))),10.);
        foam=max(foam,beachMask(uv)*wash*exp(-depth*7.)*smoothstep(.35,.75,coastNoise(uv*.7+vec2(time*.04,0.)))*.12);
        vec3 reflection=reflect(-view,normal);reflection.y=max(.002,reflection.y);
        vec2 reflectedUV=vec2(.5+atan(reflection.z,reflection.x)/6.28318530718,sqrt(clamp(asin(clamp(reflection.y,0.,1.))/1.57079632679,0.,1.)));
        vec3 reflected=mix(vec3(.07,.24,.43)*nightVisibility,texture2D(skyMap,reflectedUV).rgb,skyPhysical);
        reflected=mix(reflected,vec3(.33,.39,.47)*(.025+.975*skyDay),skyCoverage*skyStorm*.68);
        vec4 clouds=vec4(0.);if(reflectionDetail>.5)clouds=mix(texture2D(skyCloudPrevious,reflectedUV),texture2D(skyCloudMap,reflectedUV),skyCloudBlend);
        reflected=reflected*(1.-clouds.a*skyCloudEnabled)+clouds.rgb*skyCloudEnabled;
        reflected+=vec3(.002,.004,.009)*(1.-nightVisibility);
        vec3 color=waterColor*nightVisibility*(1.-fresnel)+reflected*fresnel+sunTint*glitter*sunStrength*sunReflection*solarCloudTransmission();
        color=mix(color,vec3(.67,.77,.71),foam*.45*nightVisibility);
        float distanceToEye=length(vWorld.xz-cameraPosition.xz);
        vec3 horizonColor=grazingSky(-view.xz)*mix(vec3(.97,.985,1.),vec3(.99),skyStorm);
        float aerial=1.-exp(-fogDensity*fogDensity*distanceToEye*distanceToEye);
        float edgeFade=smoothstep(20000.,100000.,distanceToEye);
        color=mix(color,horizonColor,max(aerial,edgeFade));
        // Only the sand shelf has real geometry beneath the water to transmit.
        // Thin shore film reveals grains; Fresnel retains grazing reflections.
        float shoreTransmission=beachMask(uv)*exp(-depth*3.2);
        float waterAlpha=(1.-shoreTransmission*(1.-fresnel)*.88)*smoothstep(0.,.018,depth);
        gl_FragColor=vec4(color,waterAlpha);
        #include <tonemapping_fragment>
        #include <colorspace_fragment>
      }`}),p=new x.Mesh(new x.PlaneGeometry(2,2),r);p.name="Panoramic ocean",p.position.y=2.55*w,p.frustumCulled=!1,p.raycast=()=>{},p.onBeforeRender=(E,T,_)=>{let z=r.uniforms;z.oceanCameraWorld.value.copy(_.matrixWorld),z.oceanInverseProjection.value.copy(_.projectionMatrixInverse),z.oceanProjection.value.copy(_.projectionMatrix)},e.add(p);let d=await Co(t,e,r.uniforms,E=>o(10+E*8));p.visible=!1,p.userData.study=d;let f=No({renderer:t,device:a}),g=ro();f.material.uniforms.cloudSeedOffset.value.set(g.x,g.z),f.userData.cloudLayout=g,f.material.uniforms.seaHorizon.value=1,f.userData.setCloudQuality("off"),f.renderOrder=1e3,e.add(f),p.renderOrder=-100;let u=rt(s.hour,s.date),M=ke(u.direction),v=f.material.uniforms,h=r.uniforms;v.sunPosition.value.fromArray(M),v.sunColor.value.set("#fff4e0").lerp(new x.Color("#ff7334"),u.warm),v.day.value=u.daylight,v.warm.value=u.warm,v.direct.value=u.direct,v.cloud.value=(s.weather?.cloud??.14)*no(s.hour,Wo(s.date)),v.storm.value=ge(.4,1,v.cloud.value),v.stars.value=u.night,v.radius.value=u.radius,e.fog=new x.FogExp2(new x.Color("#477b9c").lerp(new x.Color("#101b2b"),1-u.daylight),18e-6+23e-5*(1-u.daylight)),v.seaColor.value.copy(e.fog.color),f.userData.updateAtmosphere(0);for(let[E,T]of Object.entries({skyMap:"atmosphereMap",skyPrevious:"atmosphereMapPrevious",skyBlend:"atmosphereBlend",skyPhysical:"useAtmosphere",skyCloudMap:"cloudMap",skyCloudPrevious:"cloudMapPrevious",skyCloudBlend:"cloudBlend",skyCloudEnabled:"useVolumeClouds"}))(h[E]??={value:null}).value=v[T].value;h.nightVisibility.value=.06+u.daylight*.94,h.sunDirection.value.fromArray(ke(Lt(u.direction))),h.sunTint.value.copy(v.sunColor.value),h.sunStrength.value=u.direct,h.skyDay.value=u.daylight,d.setQuality(0);function y(E,T=new Date,_=0,z=.5){let P=rt(E,T),O=ke(P.direction),m=f.material.uniforms,R=r.uniforms,c=Math.max(0,Math.min(1,z)),D=ge(.4,1,c);m.sunPosition.value.fromArray(O),m.sunColor.value.set("#fff4e0").lerp(new x.Color("#ff7334"),P.warm),m.day.value=P.daylight,m.warm.value=P.warm,m.direct.value=P.direct,m.cloud.value=c,m.storm.value=D,m.stars.value=P.night,m.radius.value=P.radius,m.sidereal.value=E*Math.PI/12,m.clock.value+=_,e.fog.color.set("#477b9c").lerp(new x.Color("#101b2b"),1-P.daylight),e.fog.density=18e-6+23e-5*(1-P.daylight),m.seaColor.value.copy(e.fog.color),f.userData.updateAtmosphere(_);for(let[U,K]of Object.entries({skyMap:"atmosphereMap",skyPrevious:"atmosphereMapPrevious",skyBlend:"atmosphereBlend",skyPhysical:"useAtmosphere",skyCloudMap:"cloudMap",skyCloudPrevious:"cloudMapPrevious",skyCloudBlend:"cloudBlend",skyCloudEnabled:"useVolumeClouds"}))R[U].value=m[K].value;R.nightVisibility.value=.06+P.daylight*.94,R.sunDirection.value.fromArray(ke(Lt(P.direction))),R.sunTint.value.copy(m.sunColor.value),R.sunStrength.value=P.direct*(1-.86*D),R.skyDay.value=P.daylight,R.skyCoverage.value=c,R.skyStorm.value=D,f.userData.state={hour:E,elevation:P.elevation,cloud:c,day:P.daylight}}return{ocean:p,sky:f,study:d,waterNormal:i,setTime:y}}var jt=new URLSearchParams(location.search),Xo=jt.get("token"),Nt=xt.find(t=>t.id===jt.get("route"))||xt[0],Yo=(t,e={})=>parent.postMessage({type:t,token:Xo,...e},location.origin),Ce=Number(jt.get("hour")??yt()),Zo=300,Ut=0,Pe=!1,Ko=performance.now(),ae,q,Wt;addEventListener("message",t=>{t.origin!==location.origin||t.source!==parent||t.data?.type!=="refuge-classroom-break-clock"||t.data.token!==Xo||(Ut=Math.max(0,Number(t.data.elapsed)||0),Ce=Number(t.data.startHour??Ce),Zo=Number(t.data.duration)||300,Pe=!!t.data.playing,Ko=performance.now())});async function ja(){let t=document.getElementById("coast"),e=new Y.Scene,o=new Y.PerspectiveCamera(60,innerWidth/innerHeight,.2,12e3),a=[];ao(a);let s=a.find(u=>u.name===Nt.name),n=new Y.CatmullRomCurve3(s.positions.map(u=>new Y.Vector3(...u)),!1,"centripetal"),i=new Y.CatmullRomCurve3(s.targets.map(u=>new Y.Vector3(...u)),!1,"centripetal");ae=new Y.WebGLRenderer({canvas:t,antialias:!1,powerPreference:"low-power"}),ae.setPixelRatio(Math.min(devicePixelRatio,1.5)),ae.setSize(innerWidth,innerHeight),ae.outputColorSpace=Y.SRGBColorSpace,ae.toneMapping=Y.ACESFilmicToneMapping,ae.toneMappingExposure=1;let l=new Date;q=await qo(ae,e,()=>{},{noiseSize:32,atmosphereSize:128,cloudSize:384,cloudSteps:24,cloudInterval:650},{date:l,hour:Ce,weather:{cloud:.5,wind:8,rain:0}}),await Mo(()=>{},{phase:"entry"}),q.study.setQuality(0),q.study.settings.tide=.9,q.sky.userData.setCloudQuality("low"),await q.sky.userData.prepareClouds(()=>{},()=>Promise.resolve(),"low");let r=new Ne(o,t);r.enableDamping=!0,r.enablePan=!1;let p=!1;r.addEventListener("start",()=>{p=!0});let d=u=>{let M=so(Math.min(u,s.duration),s.duration);o.position.copy(n.getPointAt(M)),r.target.copy(i.getPointAt(M)),o.lookAt(r.target)};d(Ut),q.setTime(Ce,l,0,.5);for(let u=0;u<32;u++)q.sky.userData.updateAtmosphere(.1);q.setTime(Ce,l,0,.5),q.study.update(o,0),ae.render(e,o),t.dataset.route=Nt.id,t.dataset.ready="true",Yo("refuge-classroom-beach-ready",{route:Nt.id});let f=performance.now();function g(u){let M=Math.min(.05,Math.max(0,(u-f)/1e3));f=u;let v=Ut+(Pe?(u-Ko)/1e3:0);p?r.update():d(v),q.ocean.material.uniforms.time.value+=Pe?M:0,q.study.settings.paused=!Pe,q.study.update(o,Pe?M:0);let h=wt(Ce,v,Zo);q.setTime(h.sceneHour,new Date(+l+h.dayOffset*864e5),Pe?M:0,h.cloudCoverage),ae.render(e,o),t.dataset.hour=h.sceneHour.toFixed(6),t.dataset.dayHours=h.dayHours.toFixed(6),t.dataset.timeRate=String(h.timeRate),t.dataset.cloud=String(q.sky.material.uniforms.cloud.value),t.dataset.cloudVisible=String(q.sky.material.uniforms.useVolumeClouds.value),t.dataset.daylight=String(q.sky.material.uniforms.day.value),t.dataset.walkTime=v.toFixed(2),t.dataset.position=o.position.toArray().join(","),Wt=requestAnimationFrame(g)}Wt=requestAnimationFrame(g),addEventListener("resize",()=>{o.aspect=innerWidth/innerHeight,o.updateProjectionMatrix(),ae.setSize(innerWidth,innerHeight)}),addEventListener("pagehide",()=>{cancelAnimationFrame(Wt),r.dispose(),q.study.dispose(),ae.dispose()},{once:!0})}ja().catch(t=>{document.getElementById("coast").dataset.error=t.message,Yo("refuge-classroom-beach-error",{error:t.message}),console.error(t)});
