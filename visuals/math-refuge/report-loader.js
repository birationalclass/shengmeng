// Cache the small report manifests and decoded covers, not every board texture.
export function createReportLoader(){
  const jobs=new Map();
  return function prepare(report){
    if(jobs.has(report.id))return jobs.get(report.id);
    const job=(async()=>{
      const response=await fetch(report.manifest+'?v57-proof-flow');
      if(!response.ok)throw new Error('报告加载失败，请重试。');
      const manifest=await response.json();
      if(!manifest.pages?.length)throw new Error('报告内容为空');
      const cover=await new Promise((resolve,reject)=>{
        const image=new Image();image.onload=()=>resolve(image);
        image.onerror=()=>reject(new Error('报告封面加载失败，请重试。'));
        image.src=manifest.pages[0].formulaAsset+'?v57-proof-flow';
      });
      return {pages:manifest.pages,cover,navigation:{chapters:manifest.chapters,sections:manifest.sections,erratum:manifest.erratum}};
    })();
    jobs.set(report.id,job);
    job.catch(()=>{if(jobs.get(report.id)===job)jobs.delete(report.id);});
    return job;
  };
}
