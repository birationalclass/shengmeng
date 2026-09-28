import {GROUP_KNOWLEDGE} from './group-knowledge.mjs?v=nebula-69';
import {GROUP_DEFINITIONS} from './group-definitions.mjs?v=nebula-66';
import {levels} from './challenge-model.mjs?v=nebula-66';

export const GROUP_EXTENSIONS={
 C4:{lesson:4,zh:['C 表示 cyclic（循环）。把圆周分成四份，每次转四分之一圈，连续操作便得到全部四种旋转。','用模 4 加法记作 C₄≅ℤ/4ℤ。元素是 0̅、1̅、2̅、3̅，单位元为 0̅；加四次 1̅ 就回到起点。它是交换群，但不是每个非单位元都能生成全群。'],en:['C stands for cyclic. Repeating a quarter-turn produces all four rotations of a square.','C₄ is the additive group of integers modulo 4. Its identity is the residue of 0. It is abelian, but not every nonidentity element generates it.']},
 V4:{lesson:11,zh:['可以把元素看成两个独立开关的状态：(0,0)、(1,0)、(0,1)、(1,1)。运算就是逐位相加并模 2 化简。','每个非单位元操作两次都会复原，所以没有四阶元。它与 C₄ 同为四阶，却不是同一个群；两个不同的非单位元恰好提供两个独立方向。'],en:['Think of two independent switches. The four states form a group under addition in each coordinate modulo 2.','Every nonidentity element has order 2. Unlike C₄, this group is not cyclic: two distinct nonidentity elements supply two independent directions.']},
 S3:{lesson:12,zh:['S₃ 记录三个对象的所有重新排列，共 3!=6 种。也可以理解为正三角形的三种旋转和三种反射。','置换从右向左复合。例如 (12)(23)=(123)，而 (23)(12)=(132)，所以先后顺序影响结果。它是最小的非交换群。'],en:['S₃ contains the 3!=6 permutations of three objects. It is also the symmetry group of an equilateral triangle.','Composition is read right to left. The products (12)(23) and (23)(12) differ, illustrating the smallest non-abelian group.']},
 D4:{lesson:14,zh:['D₄ 是正方形的全部对称，共八种。令 r 为旋转 90°，s 为一次反射，元素统一写成 rⁱ 或 rⁱs，其中 0≤i<4。','关系 srs=r⁻¹ 表示反射会翻转旋转方向。先旋转再反射一般不同于先反射再旋转。两个反射相乘会成为旋转，但不一定能得到四分之一转。'],en:['D₄ consists of the eight symmetries of a square. With a quarter-turn r and a reflection s, every element is rⁱ or rⁱs, with 0≤i<4.','The relation srs=r⁻¹ says reflection reverses rotation. Two reflections give a rotation, but do not always generate the whole group.']},
 Q8:{lesson:16,zh:['Q₈ 来自四元数乘法，八个元素为 ±1、±i、±j、±k。这里的单位元是 1，且 ij=k、ji=−k。','六个元素 ±i、±j、±k 的阶都是 4，只有 −1 的阶为 2。同一轴上的正负元素生成同一个四阶循环子群；选取不同轴才能得到整个 Q₈。'],en:['Q₈ consists of ±1, ±i, ±j and ±k under quaternion multiplication. Its identity is 1, and ij=k while ji=−k.','The six elements on the i, j and k axes have order 4; only −1 has order 2. Two different axes generate the group.']},
 S4:{lesson:18,zh:['S₄ 是四个对象的全部置换，共 4!=24 个元素。选一个全长轮换 (1234) 与相邻对换 (12)，就可以生成全部置换。','“可解”指群可以经一系列正规子群分解为交换的商群。S₄ 有正规链 {e}⊲V₄⊲A₄⊲S₄，各相邻商群依次是 V₄、C₃、C₂，都交换；这里 V₄={e,(12)(34),(13)(24),(14)(23)}。','在特征零的伽罗华理论中，方程能否用根式求解由其伽罗华群的可解性决定。四次方程的伽罗华群是 S₄ 的子群，而可解群的子群仍可解，因此四次方程总有根式解。'],en:['S₄ contains the 4!=24 permutations of four objects. A full cycle (1234) and the adjacent transposition (12) generate it.','A solvable group has a normal series with abelian factors. The chain {e} ⊲ V₄ ⊲ A₄ ⊲ S₄ has factors V₄, C₃ and C₂.','In characteristic zero, Galois theory connects solvable groups to solutions by radicals. Quartic Galois groups are subgroups of the solvable group S₄.']},
 F56:{lesson:19,zh:['把 𝔽₈ 想成带有加法和乘法的八个位置。选择非零倍率 a（7 种）和位移 b（8 种），便得到可逆变换 x↦ax+b，共 56 种。','运算是变换的复合：(a,b)(c,d)=(ac,ad+b)。这些位置遵循有限域的运算法则，不能把它们直接当作模 8 整数来乘除。','本关逐个计算元素的阶可得：1 个单位元、7 个二阶元、48 个七阶元。下面仅以这份阶统计为前提，解释为何任意七阶元配二阶元就能生成全群。'],en:['An affine map x↦ax+b acts on the eight positions of the field 𝔽₈. There are seven nonzero multipliers and eight translations, giving 56 maps.','Composition is (a,b)(c,d)=(ac,ad+b). Arithmetic is in a finite field, not the integers modulo 8.','The group has one identity, seven elements of order 2 and 48 of order 7. The proof below uses this complete order count.']},
 A5:{lesson:9,zh:['A₅ 是五个对象的所有偶置换，共 5!/2=60 个。所谓偶置换，就是可以写成偶数次对换的置换；它也对应正二十面体的全部保向旋转。','A₅ 是最小的不可解群，也是非交换单群：除单位元子群与自身外没有正规子群。这使它无法沿正规子群继续拆成交换商群。','所有三轮换共同生成 A₅，但任意两个三轮换未必够用。例如 (123) 与 (124) 都固定 5，因此生成不了整个 A₅。'],en:['A₅ consists of the 5!/2=60 even permutations of five objects. It also describes the orientation-preserving rotations of an icosahedron.','It is the smallest non-solvable group and is non-abelian simple: its only normal subgroups are the identity subgroup and itself.','All 3-cycles together generate A₅, but an arbitrary pair need not. For example, (123) and (124) both fix 5.']},
 S5:{lesson:18,zh:['S₅ 是五个对象的全部置换，共 5!=120 个。一个全长轮换 (12345) 与相邻对换 (12) 就足以生成全部元素。','它含有不可解的正规子群 A₅，因此本身不可解。伽罗华理论说明：一般五次方程没有根式通解。这里不排除特殊五次方程有根式解，例如 x⁵−2=0。','“没有根式通解”并不表示无法数值求根；它限制的是通过有限次四则运算与开方来表达一般方程根的方式。'],en:['S₅ contains the 5!=120 permutations of five objects. The full cycle (12345) and adjacent transposition (12) generate all of them.','Its non-solvable normal subgroup A₅ makes S₅ non-solvable. Hence the general quintic has no solution formula by radicals; special quintics can still be solvable.','This does not prevent numerical root finding. It concerns expressing general roots using finitely many arithmetic operations and root extractions.']}
};

export function extensionUnlocked(key,journey,groups){
 return Boolean(groups[key] && (journey[key]?.passed||0)>=levels(groups[key]).length);
}

export function mountGroupExtension({t,getGalaxy,getJourney,groups}){
 const button=document.createElement('button');
 button.id='sectorExtension';button.type='button';
 button.innerHTML='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.4" aria-hidden="true"><path d="M14 4h6v6M20 4l-9 9M10 5H4v15h15v-6"/></svg>';
 document.getElementById('sectorDefinition').after(button);
 const dialog=document.createElement('dialog');dialog.id='groupExtension';dialog.className='cosmic-dialog';
 dialog.setAttribute('aria-labelledby','extensionTitle');
 dialog.innerHTML='<button class="cosmic-close" type="button">×</button><p class="dialog-eyebrow">BEYOND THE STARS</p><h2 id="extensionTitle"></h2><div class="extension-formula"></div><div class="extension-content"></div>';
 document.body.append(dialog);
 dialog.querySelector('button').onclick=()=>dialog.close();
 function fill(){
  const g=getGalaxy(),data=GROUP_EXTENSIONS[g.key];
  dialog.querySelector('button').setAttribute('aria-label',t('关闭','Close'));
  dialog.querySelector('h2').textContent=g.name+' · '+t(g.zh,g.en);
  const formula=dialog.querySelector('.extension-formula');
  if(window.katex)window.katex.render(GROUP_DEFINITIONS[g.key],formula,{displayMode:true,throwOnError:false});else formula.textContent=GROUP_DEFINITIONS[g.key];
  const body=dialog.querySelector('.extension-content');body.replaceChildren();
  function add(tag,text){const el=document.createElement(tag);for(const part of text.split(/([0-3]̅)/)){if(/^[0-3]̅$/.test(part)&&window.katex){const span=document.createElement('span');window.katex.render('\\bar{'+part[0]+'}',span,{throwOnError:false});el.append(span);}else el.append(document.createTextNode(part));}body.append(el);}
  t(data.zh,data.en).forEach(p=>add('p',p));
  const lesson=GROUP_KNOWLEDGE[data.lesson];
  add('h3',t('生成元与证明','Generators and proof (Chinese)'));
  add('p',lesson.statement.replace('本关取 n=4 或 5','本关取 n='+g.key.slice(1)));
  lesson.proof.split(/\n\n/).forEach(p=>add('p',p));
  add('p',lesson.hint);
 }
 button.onclick=()=>{if(!extensionUnlocked(getGalaxy().key,getJourney(),groups))return;fill();dialog.showModal();dialog.scrollTop=0;};
 return {sync(){
  const enabled=extensionUnlocked(getGalaxy().key,getJourney(),groups);
  button.disabled=!enabled;button.classList.toggle('unlocked',enabled);
  const label=enabled?t('展开详细介绍','Explore this group'):t('完成本星系全部难度后解锁介绍','Complete every difficulty in this galaxy to unlock');
  button.title=label;button.setAttribute('aria-label',label);
  if(dialog.open){if(enabled)fill();else dialog.close();}
 }};
}
