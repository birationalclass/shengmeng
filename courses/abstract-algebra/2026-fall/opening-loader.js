/* Heavy opening assets are not requested when entering a lesson directly. */
(()=>{
  const sources=[
    "./opening-polyhedra.js?v=20260913-galois-seven-scenes",
    "./opening-topology.js?v=20260913-topology-framing",
    "./opening-gauss.js?v=20260913-galois-seven-scenes",
    "./opening-galois-portrait.js?v=20260913-galois-seven-scenes",
    "./opening-galois-story.js?v=20260914-galois-education",
    "./opening-lettering-data.js?v=20260914-unified-type",
    "./opening-galois.js?v=20260914-unified-type",
    "./opening-geometry.js?v=20260914-rings-fine-signature",
    "./opening-impulse.js?v=20260913-galois-seven-scenes",
    "./opening-materials.js?v=20260919-course-polish-v1",
    "./opening-timeline.js?v=20260913-galois-seven-scenes",
    "./opening-motion.js?v=20260913-galois-seven-scenes",
    "./opening-playlist.js?v=20260913-galois-seven-scenes",
    "./opening-camera.js?v=20260921-lie-framing",
    "./opening-audio-preload.js?v=20260919-course-polish-v1",
    "./opening-galois-audio.js?v=20260919-course-polish-v1",
    "./opening-audio.js?v=20260919-opening-controls-v1",
    "./opening-backdrop.js?v=20260914-rings-fine-signature",
    "./opening-voice.js?v=20260915-voice-timing-v1",
    "./opening-outro.js?v=20260919-section-loading-v1",
    "./opening-narration.js?v=20260919-opening-controls-v1",
    "./opening-galois-timeline.js?v=20260914-galois-education",
    "./opening-inscription.js?v=20260914-rings-fine-signature",
    "./opening-fonts.js?v=20260915-course-title-v5",
    "./opening.js?v=20260919-course-polish-v1"
];
  let loading=null;
  function load(){
    if(loading)return loading;
    loading=Promise.all(sources.map(src=>new Promise((resolve,reject)=>{
      const node=document.createElement('script');node.src=src;node.async=false;
      node.onload=resolve;node.onerror=()=>reject(new Error('Opening asset failed: '+src));
      document.head.append(node);
    })));
    return loading;
  }
  async function replay(){
    if(window.CourseOpeningOpen){window.CourseOpeningOpen();return;}
    window.courseOpeningControllerLazy=true;window.courseOpeningDismissed=false;window.CourseOpeningBoot.start();
    try{await load();if(document.querySelector('#courseOpening').open&&!window.courseOpeningDismissed)window.CourseOpeningOpen();}
    catch(error){console.error(error);window.CourseOpeningBoot.dismiss();}
  }
  document.querySelector('[data-replay-opening]').addEventListener('click',replay);
  if(!location.hash&&new URLSearchParams(location.search).get('view')!=='lesson'&&!window.courseOpeningDismissed)load().catch(error=>{console.error(error);window.CourseOpeningBoot.dismiss();});
})();
