# Actual varied-twist polynomial matrix top-Cech duality

Let K be a field,sigma finite and ordered,card(sigma)=r+1,r>=1,
P=Proj K[sigma],B=Gamma(Spec K,O),Phi:K~=B the canonical ring map.
Let I,J be finite,a_i,b_j>=0 arbitrary and p_ij homogeneous of degree
a_i-b_j when nonnegative;the corresponding entry is ZERO if a_i<b_j.
Write A=direct_sum_i T(-a_i-r-1),C=direct_sum_j T(-b_j-r-1).
M:A->C is the ACTUAL original sheaf matrix of polynomial multiplication.
Write D_a:H_Cech^r(A)~=direct_sum_i S_(a_i)(B)^dual and similarly D_b.
Let N be the matrix of actual homogeneous multiplication transposes,
with the canonical Phi applied to polynomial coefficients. Then
D_b o H_Cech^r(M)=N o D_a.

The actual Cech/homology functor preserves finite biproduct assembly.
Actual original sheaf degree transports match the independently
constructed complex degree transports. The prior polynomial transpose
formula supplies each entry;the negative multiplying-degree case is
proved zero. No ordering of all twists or uniform twist is assumed.
No homology or multiplication matrix is defined through duality.
The actual cokernels are isomorphic and their quotient maps commute:
coker(H_Cech^r(M))~=coker(N).

This is the varied FREE-TWIST matrix case. It does NOT identify
H_Cech^r(coker(M)) with coker(H_Cech^r(M)). Actual affine exactness and
top-Cech descent for coherent sheaf presentations remain to prove,
as do derived sheaf-cohomology comparison and original Koszul
connecting-map/restriction compatibility. Original4.1 canonical
normalized-dualizing identification stays UNVERIFIED;original4.1/4.2
and the main theorem remain OPEN. No normality,smoothness or CM
condition is added to the original integral complex V.

8 new modules;405 physical source lines;25 audited
declarations (13 proofs and 12 definitions).
131 closed modules;123 older dependencies
match previously frozen bytes. Exact types and transitive axioms are
included:only propext,Classical.choice,Quot.sound. Every local compile
and audit uses lean_runner.run_file,one compiler,8GiB Job,2threads,
CPU<=25%,20minutes. No whole-project checkpoint/Lean CI is asserted.
Pinned Lean v4.35.0-rc3;mathlib2a885768dae569d938bb9ff3474da6a8753bb90a.
Original manuscript SHA256:
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Compile closed modules in dependency order,then CheckAxioms.lean.
Linear.lean is the convenience entry. Previous Apache2.0 attribution
is preserved. No downloaded setup program is executed.
