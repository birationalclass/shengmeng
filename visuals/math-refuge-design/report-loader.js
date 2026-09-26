import {fetchLocal,decodeImage} from './mobile-runtime.js?v79-mobile';
// Cache the small report manifests and decoded covers, not every board texture.
export function createReportLoader(){
  const jobs=new Map();
  return function prepare(report){
    if(jobs.has(report.id))return jobs.get(report.id);
    const job=(async()=>{
      const manifest=JSON.parse(await fetchLocal(report.manifest+'?v62-chalk-ink'));
      if(!manifest.pages?.length)throw new Error('报告内容为空');
      const cover=await decodeImage(manifest.pages[0].formulaAsset+'?v62-chalk-ink');
      return {pages:manifest.pages,cover,navigation:{chapters:manifest.chapters,sections:manifest.sections,erratum:manifest.erratum}};
    })();
    jobs.set(report.id,job);
    job.catch(()=>{if(jobs.get(report.id)===job)jobs.delete(report.id);});
    return job;
  };
}
