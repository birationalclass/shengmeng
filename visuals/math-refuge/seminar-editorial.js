// Each cue is tied to a specific board, rather than inferred from keywords.
// c = dashed frame (legacy cue key), u = underline, b = bracket. Labels remain bilingual.
const cues={
meng:`c|两个方向|Two directions
u|沿对角线|Sum diagonally
c|闭元模边界|Cycles / boundaries
b|微分保持滤过|Preserved by D
c|取像，不是全体|Take the image
c|相邻层取商|Adjacent quotient
b|先检查包含|Check inclusion
c|代表元有条件|Filtered representatives
u|总次数加一|Total degree +1
u|再取上同调|Take cohomology
b|固定一个位置|Fix a bidegree
c|只剩纵向微分|Vertical differential
u|得到关联分次|Associated graded
b|只有一行|One surviving row
c|光滑，不必全纯|Smooth coefficients
u|反交换是关键|Anticommutation
u|先取 Dolbeault|Dolbeault first
c|滤过商|Filtration quotient
b|紧 Kähler 假设|Compact Kähler
u|与代表元无关|Independent of choices
u|纯型分解|Decompose by type
b|两个空间|Two spaces
c|先取内射分解|Injective resolution
c|逐项取直像|Direct image of terms
b|核与像都是层|Sheaf kernels / images
u|准备拼接|Prepare the resolutions
b|两次马蹄引理|Horseshoe twice
c|相容的双复形|Compatible maps
u|现在取截面|Now take sections
c|别漏掉符号|Keep the sign
u|先纵向，再横向|Vertical, then horizontal
c|第二页的识别|Identify page two
u|换方向计算|Use the other direction
u|识别收敛目标|Identify the abutment
b|充分正扭曲|Sufficiently positive twist
u|高阶直像消失|Higher images vanish`,
hu:`b|几何假设|Hypotheses
c|Cartier 与 nef|Cartier and nef
u|降低亏格门槛|Lower the threshold
c|纤维连通|Connected fibres
b|门槛不能删|Keep the threshold
u|等号限制纤维|Equality constrains fibres
u|先排除一个分支|Exclude this branch
b|共同的数值起点|Numerical starting point
c|中间上同调|Intermediate cohomology
u|还需控制示性数|Control the Euler term
b|次数是整数|Degree is integral
c|两个参数|Two parameters
u|这里是严格不等式|Strict inequality
u|加性估计更强|Use the additive bound
b|映射相容|Compatible maps
c|生成秩|Generated rank
u|限制底曲线亏格|Bound the base genus
c|两个次数相乘|Multiply the degrees
u|曲面次数上界|Surface degree bound
b|选最大的零除子|Maximal zero divisor
u|一般点与扭曲|General points and twist
u|二次界闭合|Close the degree bound
b|两处都要取等号|Both bounds are sharp
c|上界可以达到|The bound is attained`,
ye:`b|先规定原点值|Value at the origin
b|阶数固定|Fix the order
c|非负号约定|Nonnegative convention
b|按奇偶分开|Separate parity cases
c|能量比下确界|Infimum of quotients
u|尺度不同|Different scales
u|首项系数也要匹配|Match the coefficient
c|转到环面|Move to the torus
b|连续算子|Continuous operator
u|记住换算因子|Keep the conversion factor
b|参数范围|Parameter range
u|一步的代价|Cost of one step
c|展开一个平方|Expand a square
b|Hessian 项不能丢|Keep the Hessian term
c|归一化权|Normalized weight
u|指数小的坏区域|Exponential concentration
u|小概率还不够|Probability is not enough
b|常数与维数无关|Dimension-free constant
c|均值需要重估|Re-estimate the mean
b|保权与降权|Keep or lower the weight
u|连接两种奇偶|Bridge the parity cases
u|固定次数迭代|Finitely many steps
c|只需一个试验函数|One test function
u|上下界相遇|Matching bounds`,
duan:`b|粒子与孤子|Particles and solitons
c|不再是群乘法|Beyond group multiplication
b|偶与奇分别记录|Keep both parities
c|看自同态超代数|Endomorphism superalgebra
b|保留费米奇偶性|Retain fermion parity
c|图变成算符|A diagram is an operator
u|交换奇交点有负号|Odd interchange: minus
c|相容性投影|Compatibility projector
b|还要检查奇偶反转|Check parity reversal
u|同一多重态同质量|Equal mass in a multiplet
b|线类型与交点不同|Line type versus junction
c|保留 Majorana 模|Keep the Majorana mode
u|两个方向，共四态|Four states, two directions
b|只取特定形变|A specific deformation
c|Chebyshev 结构|Chebyshev structure
u|临界点给出真空|Critical points give vacua
b|筛选保留的线|Select surviving lines
c|保留奇偶分次|Keep the grading
b|两种对称性互补|Complementary symmetries
u|规范化与形变相容|Gauging and deformation
c|带符号的真空计数|Signed vacuum count
b|实超场|Real superfield
b|负耦合的有隙分支|Negative, gapped branch
c|奇偶交替|Alternating parity
u|检查指标一致性|Check the indices
c|局域作用|Localized action
u|相位差给出分数部分|Phase difference
b|这里是整数型|Integral in this case
u|态转成边界算符|States to boundary operators
b|三种边界角色|Three boundary roles
c|统计信息仍保留|Statistics remain
b|约束不等于完整谱|Constraints, not full spectra`
};

export const wording=[
['本文将得到次数上界所需的几何亏格门槛大幅降低。','目标是在更低的几何亏格门槛下得到次数上界。'],
['The paper strengthens the large-genus result by reducing the required threshold for geometric genus.','We seek the degree bound under a lower geometric-genus threshold.'],
['文中指出，小几何亏格时存在典范次数为 96 的例子。','小几何亏格时存在典范次数为 96 的例子。'],
['the paper notes examples of canonical degree 96','there are examples of canonical degree 96'],
['文中引用的 Chen–Hacon (2006) 估计','Chen–Hacon (2006) 估计'],
['the Chen–Hacon (2006) estimate cited in the paper','the Chen–Hacon (2006) estimate'],
['本文关注非可逆对称性破缺、费米奇偶性仍保留的相。','以下考虑非可逆对称性破缺、费米奇偶性仍保留的相。'],
['右图重绘原文的表示箭图；这些箭头表示激发，不是经典轨迹。','箭图中的箭头表示真空之间的激发，不是经典轨迹。'],
['The redrawn quiver records excitations between vacua, not classical trajectories.','The quiver records excitations between vacua, not classical trajectories.'],
['固定原文的形变尺度','固定形变的总体尺度'],
['Use the deformation scale fixed in the paper.','Fix the overall deformation scale.'],
['所示质量采用原文归一化','质量按所示超势归一化'],
["The mass shown uses the paper’s normalization; restoring the overall scale rescales every mass.",'The mass is normalized by the displayed superpotential; restoring the overall scale rescales every mass.'],
['此式采用原文的代表元约定；物理多重态不依赖代表元选择。','这里固定轨道代表元；物理多重态不依赖这一选择。'],
["This uses the paper’s orbit representatives; physical multiplets are independent of that choice.",'Fix orbit representatives; physical multiplets are independent of that choice.'],
['原文的二重超对称例子中','这些二重超对称例子中'],
['原文选择负耦合的有隙分支','取负耦合的有隙分支'],
['The paper takes the negative-coupling gapped branch.','Take the negative-coupling gapped branch.'],
['按原文约定，偶标签的 m 型真空与奇标签的 q 型真空交替排列。','取偶标签为 m 型、奇标签为 q 型，真空依次交替排列。'],
["In the paper’s convention, even labels give m-type vacua and odd labels q-type vacua.",'Even labels give m-type vacua and odd labels give q-type vacua.'],
['指标的整体符号沿用原文；','固定所示指标的整体符号；'],
["Signs follow the paper’s convention.",'Use the displayed overall sign convention.'],
['原文得到整数型费米数','得到整数型费米数'],
['the paper finds integral fermion number','the fermion number is integral'],
['右图是原文立体构造的简化截面示意。','右图用截面表示体理论与边界之间的关系。'],
["The drawing simplifies the paper’s bulk construction.",'The section shows the relation between the bulk and its boundaries.'],
['在讲义给定的特征零、射影双有理设定下','在特征零的射影双有理设定下']
];
export function refineSeminarPage(page,report,index){
  const clean=s=>wording.reduce((text,[a,b])=>text.replaceAll(a,b),s||'');
  const result={...page,text:clean(page.text),en:{...page.en,text:clean(page.en?.text)}};
  if(!page.kind){
    const cue=cues[report]?.split('\n')[index-1];
    if(!cue)throw new Error(`Missing editorial cue: ${report}/${index}`);
    const [mark,zh,en]=cue.split('|');
    const focusRows={
      meng:{1:1,3:2,5:2,12:1,15:1,18:2,30:2,32:1},
      hu:{4:1,9:1,16:1,18:1,24:1},
      ye:{3:1,13:1,19:1},
      duan:{2:1,4:1,6:1,8:1,12:1,18:1,24:1,26:1,31:1}
    };
    result.annotation={mark,label:{zh,en},row:focusRows[report]?.[index]??(mark==='u'?-1:0)};
  }
  return result;
}
