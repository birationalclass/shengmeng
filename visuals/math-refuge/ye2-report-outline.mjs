import {yeReport} from './ye-report-outline.mjs';
const R=String.raw;
// Independently checked finite-support calculation; no sharpness claim for this example.
const example={source:'例子 · 一维',title:'先算一个三项序列',editorialIndex:2001,voiceSection:100,voiceParagraphStart:0,
 en:{source:'EXAMPLE',title:'One finite sequence',text:'Only the first entry contributes\nOne example gives only an upper bound'},
 boardLines:[
  {tex:R`u_0=0,\quad u_1=1,\quad u_n=0\ (n\ge2)`},
  {tex:R`E(u)=1^2+(-1)^2=2`},
  {text:'加权量 M(u)=1：只有第一项有贡献',enText:'Weighted mass M(u)=1: only the first entry'},
  {tex:R`E(u)/M(u)=2`},
  {text:'例子只给上界；下界要对全部序列成立',enText:'One upper bound / a lower bound for every sequence'}
 ],
 tex:R`\begin{gathered}u_0=0,\quad u_1=1,\quad u_n=0\ (n\ge2)\\E(u)=1^2+(-1)^2=2\\E(u)/M(u)=2\end{gathered}`,
 text:'加权量 M(u)=1：只有第一项有贡献\n例子只给上界；下界要对全部序列成立',
 readingText:'独立算例：序列只有第一个位置非零；两个相邻差分给出能量2，加权量1，商2。这个例子不达到 Hardy 最佳系数1/4。',
 strictLineCount:true,mainLineCount:6,extraMathLines:0,formulaAlign:'center'};
// Reuse verified mathematics, not another generated copy of the source proof.
export const ye2Report=[{...yeReport[0],source:'报告2 · 亲切交流'},example,...yeReport.slice(1)];
