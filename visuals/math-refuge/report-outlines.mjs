import {yeReport} from './ye-report-outline.mjs';
import {huReport} from './hu-report-outline.mjs';
// Bilingual seminar summaries, adapted from the two CC BY 4.0 preprints.
// These are concise boards, not a transcript or an assertion of a live event.
export const reportOutlines={
  ye:yeReport,
  hu:huReport
};
// Section identifiers retain the paper numbering in either language.
for(const pages of Object.values(reportOutlines))for(const p of pages)if(p.kind!=='cover')p.en.source=p.source.replace('定理','Theorem').replace('引理','Lemma').replace('推论','Corollary').replace('命题','Proposition').replace('情形','Case').replace('未满秩','deficient rank').replace('满秩','full rank').replace('底曲线估计','base-map estimate').replace('证明收束','conclusion').replace('例','Example').replace('术语','terminology').replace('记号','notation').replace('曲面次数','surface degree');
