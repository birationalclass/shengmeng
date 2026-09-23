// Sparse, authored definition cues. Unlisted pages intentionally have no marks.
// focus = [left, top, width, height] within the selected formula row, measured
// from the SVG glyph bounds. Recheck these bounds when changing the listed term.
const cues={
  meng:{
    5:{row:1,term:'F^pH^n',focus:[.021955,.064462,.626302,.782438]},
    7:{row:0,term:'Z_r^{p,q}',focus:[.007719,.174945,.103730,.775152]},
    8:{row:0,term:'E_{r}^{p,q}',focus:[.008444,.282859,.157246,.340885]},
    15:{row:1,term:'\\mathcal A^{p,q}(X)',focus:[.008367,.053571,.310115,.892857]},
    24:{row:0,term:'\\mathcal{A}^\\bullet',focus:[.017654,.056980,.232833,.738875]},
    25:{row:2,term:'\\mathcal{H}^q',focus:[.007465,.075452,.113430,.690620]}
  },
  hu:{
    16:{row:1,term:'r=\\operatorname{rank}(\\operatorname{im}\\mathrm{ev})',focus:[.635237,.300838,.356482,.659587],color:'u',label:{zh:'生成秩',en:'Generated rank'}}
  },
  ye:{
    2:{row:0,term:'\\mathcal E(\\mathbb Z^d)',focus:[.005847,.047140,.151688,.905753]},
    5:{row:0,term:'\\mathcal C_{m,d}',focus:[.004597,.333668,.110768,.343936]},
    8:{row:1,term:'\\omega(x)',focus:[.008035,.329153,.197527,.313050]},
    15:{row:0,term:'\\rho=2\\omega/d',focus:[.004479,.329074,.214361,.313195]},
    18:{row:0,term:'\\operatorname{Ent}_\\mu(f^2)',focus:[.006119,.258629,.275907,.447325]}
  },
  duan:{
    3:{row:0,term:'\\mathbb C^{n|m}',focus:[.362062,.043766,.103485,.700427]},
    4:{row:1,term:'\\operatorname{Cl}_1',focus:[.343474,.090736,.085965,.738852]},
    6:{row:0,term:'\\operatorname{sStr}_{\\mathscr C}(\\mathcal M)',focus:[.337954,.053571,.638720,.892857],color:'b',label:{zh:'超条带代数',en:'Super strip algebra'}},
    21:{row:0,term:'I_W',focus:[.008824,.222248,.121887,.653689]}
  }
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
  delete result.annotation;
  const cue=!page.kind&&cues[report]?.[index];
  if(cue){
    if(!page.tex.includes(cue.term))throw new Error(`Recheck definition focus: ${report}/${index}`);
    result.annotation={mark:'c',...cue};
  }
  return result;
}
