import {configureCoursePacks} from './course-pack-cache.js';
import {resourceFetch} from './resource-fetch.js';
import {fetchLocal,decodeImage} from './mobile-runtime.js?v79-mobile';
// Cache the small report manifests and decoded covers, not every board texture.
export function createReportLoader(){
  const jobs=new Map();
  return function prepare(report){
    if(jobs.has(report.id))return jobs.get(report.id);
    const job=(async()=>{
      await configureCoursePacks(report,{fetcher:resourceFetch});
      const manifest=JSON.parse(await fetchLocal(report.manifest+'?v='+(report.kind==='classroom'?'eraser-sync-orbits-20261015':'report-line-sync-6')));
      if(!manifest.pages?.length)throw new Error('报告内容为空');
      const cover=await decodeImage(manifest.pages[0].formulaAsset+'?v=report-line-sync-6');
      return {pages:manifest.pages,cover,navigation:{chapters:manifest.chapters,sections:manifest.sections,erratum:manifest.erratum}};
    })();
    jobs.set(report.id,job);
    job.catch(()=>{if(jobs.get(report.id)===job)jobs.delete(report.id);});
    return job;
  };
}
