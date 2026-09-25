// Mock grading data. This module is the boundary for a future independent grading service.
export function getDemoQuestion(subject, student, question = 0){
  if(subject==='secondary') return question===0?{
    title:'一元二次方程 · 单元练习',course:'初三数学 · 三年级（2）班',paper:'数学单元练习',topic:'解方程',number:12,
    prompt:'解方程：<span class="math">x² − 5x + 6 = 0</span>，请写出计算过程。',
    lines:student===1?['解：x² − 5x + 6 = 0','(x − 2)(x − 3) = 0','所以 x = 2 或 x = 3']:['解：x² − 5x + 6 = 0','(x − 2)(x − 3) = 0','所以 x = −2 或 x = −3'],
    criteria:[['因式分解',3,'正确分解为两个一次因式。'],['求根过程',4,'运用了两因式乘积为零的性质。'],['最终结果',3,'最后一行的根需要核对符号。']],
    feedback:'因式分解正确。请把求出的根代回原方程，检查符号是否正确。',annotation:'根的符号需要核对',warning:'核对最终结果的符号，再确认得分。'
  }:{title:'一元二次方程 · 单元练习',course:'初三数学 · 三年级（2）班',paper:'数学单元练习',topic:'判别式',number:13,prompt:'求方程 <span class="math">x² − 4x + 4 = 0</span> 的判别式，并判断根的情况。',lines:['解：a = 1，b = −4，c = 4','Δ = b² − 4ac = 16 − 16 = 0','所以方程有两个相等的实数根。'],criteria:[['识别系数',3,'正确识别三个系数。'],['计算判别式',4,'判别式计算正确。'],['判断根',3,'对根的情况判断正确。']],feedback:'判别式计算和结论均正确，过程清楚。',annotation:'计算与结论一致',warning:''};
  if(subject==='general')return question===0?{title:'阅读与表达 · 课堂练习',course:'综合示例 · 教学班 A',paper:'课堂练习',topic:'简答题',number:3,prompt:'材料：社区图书馆延长开放时间，并增设无障碍通道。请概括这两项措施的作用。',lines:['延长时间，让更多人有机会来读书。','无障碍通道方便行动不便的人进入。','图书馆的藏书数量也会增加。'],criteria:[['概括第一项措施',3,'说明延长开放时间带来的便利。'],['概括第二项措施',4,'说明无障碍设施的作用。'],['依据材料表达',3,'新增藏书的判断缺少材料依据。']],feedback:'前两点概括清楚。最后一点请回到材料寻找依据，避免补充材料没有说明的信息。',annotation:'这句话在材料中没有依据',warning:'按教师评分标准核对无依据表述的扣分。'}:{title:'阅读与表达 · 课堂练习',course:'综合示例 · 教学班 A',paper:'课堂练习',topic:'概括题',number:4,prompt:'用一句话概括：学生自发整理图书、修补旧书，并开展图书交换活动。',lines:['学生通过整理、修补和交换图书，','共同维护并分享阅读资源。'],criteria:[['主体',3,'包含学生这一主体。'],['行为',4,'概括主要活动。'],['表达',3,'句意完整，表达简洁。']],feedback:'概括完整，表达简洁。',annotation:'要点完整',warning:''};
  return question===0?{title:'微积分 · 第三周作业',course:'高等数学 A · 数学系 2026 级',paper:'高等数学 A · 第三周作业',topic:'分部积分',number:3,prompt:'求不定积分 <span class="math">∫ x eˣ dx</span>，并写出主要步骤。',lines:student===1?['解：令 u = x，dv = eˣ dx，','则 du = dx，v = eˣ。','∫ x eˣ dx = xeˣ − ∫ eˣ dx','= xeˣ − eˣ + C。']:['解：令 u = x，dv = eˣ dx，','则 du = dx，v = eˣ。','∫ x eˣ dx = xeˣ − ∫ eˣ dx','= xeˣ + eˣ + C。'],criteria:[['选择方法',3,'选取 u 与 dv 正确。'],['分部积分',4,'公式使用及代入过程正确。'],['最终结果',3,'末行的正负号需要核对。']],feedback:'分部积分的思路和代入都正确。请检查最后一步积分前的负号，也可以对结果求导进行验证。',annotation:'此处应为 −eˣ，请核对',warning:'最后一行与上一步符号不一致，请对照原卷复核。'}:{title:'微积分 · 第三周作业',course:'高等数学 A · 数学系 2026 级',paper:'高等数学 A · 第三周作业',topic:'极限计算',number:4,prompt:'计算极限 <span class="math">lim (x→0) sin x / x</span>，说明依据。',lines:['解：当 0 < x < π/2 时，','cos x ≤ sin x / x ≤ 1。','由夹逼定理，右极限为 1。','函数为偶函数，所以两侧极限均为 1。'],criteria:[['建立不等式',3,'给出适用区间及夹逼关系。'],['运用定理',4,'正确运用夹逼定理。'],['两侧极限',3,'用偶性补充左侧极限。']],feedback:'依据完整，同时考虑了两侧极限。',annotation:'两侧极限说明完整',warning:''};
}

export function getDemoGrade(subject, student, index) {
 const q=getDemoQuestion(subject,student,index);
 const correct=index===1||(student===1&&subject!=="general");
 return {scores:correct?[3,4,3]:[3,4,1], feedback:correct&&index===0?"过程完整，结果正确。可以用代回或求导的方法进一步检验。":q.feedback, confirmed:false};
}
