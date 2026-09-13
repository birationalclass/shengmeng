/* Local, short-lived sand displacement. A click never changes the geometry. */
(function(host){
  'use strict';
  const lifetime=1.9;
  const smooth=(a,b,x)=>{const t=Math.max(0,Math.min(1,(x-a)/(b-a)));return t*t*(3-2*t);};
  function fromScreen(x,y,width,height,view,spin){
    const aspect=width/height,fit=Math.min(.68,aspect*.84)*view.zoom,t=Math.max(0,Math.min(1,(aspect-.8)/.5)),centre=.05+.15*t*t*(3-2*t);
    let p=[(2*x/width-1)*aspect/fit,(1-2*y/height-centre)/fit,0];
    const rz=a=>{const c=Math.cos(a),s=Math.sin(a);p=[c*p[0]-s*p[1],s*p[0]+c*p[1],p[2]];};
    rz(-view.angles[2]);
    {const a=-view.angles[0],c=Math.cos(a),s=Math.sin(a);p=[p[0],c*p[1]-s*p[2],s*p[1]+c*p[2]];}
    {const a=-view.angles[1],c=Math.cos(a),s=Math.sin(a);p=[c*p[0]+s*p[2],p[1],-s*p[0]+c*p[2]];}
    p=p.map((v,i)=>v+view.target[i]);rz(-spin);
    return {origin:p,radius:.45/view.zoom};
  }
  function create(){
    let events=[];
    function active(time){return events.some(e=>time>=e.time&&time-e.time<lifetime);}
    function trigger(origin,radius,time){events=events.filter(e=>time-e.time<lifetime).slice(-3);events.push({origin:[...origin],radius,time});}
    function offset(point,time,seed=0){
      const out=[0,0,0];
      for(const e of events){
        const age=time-e.time;if(age<0||age>=lifetime)continue;
        const d=point.map((v,i)=>(v-e.origin[i])*(i===2?.45:1)),distance=Math.hypot(...d),q=distance/e.radius;
        const elapsed=Math.max(0,age-.12*Math.min(q,2));
        const strength=e.radius*.85*Math.exp(-q*q*2)*(1-Math.exp(-elapsed/.055))*(1-smooth(.15,1.65,elapsed));
        const direction=distance>1e-5?d.map(v=>v/distance):[Math.cos(seed*6.28318530718),Math.sin(seed*6.28318530718),0];
        for(let i=0;i<3;i++)out[i]+=direction[i]*strength;
      }
      return out;
    }
    function uniforms(){const values=new Float32Array(16),radii=new Float32Array(4);events.forEach((e,i)=>{values.set([...e.origin,e.time],i*4);radii[i]=e.radius;});return {values,radii};}
    return {trigger,offset,active,uniforms,clear(){events=[];},evidence:()=>events.map(e=>({...e,origin:[...e.origin]}))};
  }
  const shader=`
    uniform vec4 impulses[4];
    uniform float impulseRadii[4];
    vec3 impulseOffset(vec3 p){
      vec3 result=vec3(0.);
      for(int i=0;i<4;i++){
        float age=time-impulses[i].w,radius=impulseRadii[i];
        if(radius>.00001&&age>=0.&&age<1.9){
          vec3 d=(p-impulses[i].xyz)*vec3(1.,1.,.45);float distance=length(d),q=distance/radius;
          float elapsed=max(0.,age-.12*min(q,2.));
          float strength=radius*.85*exp(-q*q*2.)*(1.-exp(-elapsed/.055))*(1.-smoothstep(.15,1.65,elapsed));
          vec3 direction=distance>.00001?d/distance:vec3(cos(grain.x*6.28318530718),sin(grain.x*6.28318530718),0.);
          result+=direction*strength;
        }
      }
      return result;
    }`;
  host.CourseOpeningImpulse=Object.freeze({create,fromScreen,lifetime,shader});
})(typeof window!=='undefined'?window:globalThis);
