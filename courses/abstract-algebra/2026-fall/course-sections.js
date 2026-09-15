/* Section titles follow the third-edition textbook, Chapters 1–4. */
window.CourseSections=[
 ['1.1','等价关系与集合的分类','Equivalence relations and partitions'],
 ['1.2','群的概念','The concept of a group'],
 ['1.3','子群','Subgroups'],['1.4','群的同构','Group isomorphisms'],['1.5','循环群','Cyclic groups'],['1.6','置换群与对称群','Permutation and symmetric groups'],['1.7','置换在对称变换群中的应用','Applications of permutations to symmetry groups'],
 ['2.1','子群的陪集','Cosets of a subgroup'],['2.2','正规子群与商群','Normal subgroups and quotient groups'],['2.3','群的同态和同态基本定理','Homomorphisms and the first isomorphism theorem'],['2.4','群的直积','Direct products of groups'],['2.5','群在集合上的作用','Group actions on sets'],['2.6','西罗定理','Sylow theorems'],['2.7','自由群与群的表达','Free groups and group presentations'],
 ['3.1','环的定义与基本性质','Rings: definition and basic properties'],['3.2','整环、域与除环','Integral domains, fields and division rings'],['3.3','理想与商环','Ideals and quotient rings'],['3.4','环的同态','Ring homomorphisms'],['3.5','素理想与极大理想','Prime and maximal ideals'],['3.6','环的特征与素域','Characteristic and prime fields'],
 ['4.1','多项式环','Polynomial rings'],['4.2','整环的商域','Fields of fractions'],['4.3','唯一分解整环','Unique factorization domains'],['4.4','主理想整环与欧几里得整环','Principal ideal and Euclidean domains'],['4.5','唯一分解整环上的多项式环','Polynomials over a unique factorization domain']
].map(([id,zh,en])=>({id,title:[zh,en],ready:id==='1.1'||id==='1.2'}));
