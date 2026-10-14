# Original presentation: Cech and homogeneous Hom prefixes

These are TWO proved prefixes,not yet one coherent duality identification.

ALGEBRA. Let K be a field,S a nonnegatively graded K-algebra,and
R=sum_i S(-z_i),E=sum_j S(-w_j) original finite shifted-free modules.
Let M be originally integer graded,c:R->E,b:E->M original degree-zero
maps,b onto,and range(c)=ker(b). For every integer d,the ORIGINAL
Hom_S(M,S)_d is the ACTUAL transpose multiplication kernel Delta_d,
with u_j in S_(w_j+d),row_i=sum_j c(e_i)_j*u_j in S_(z_i+d).
The ACTUAL categorical coker(Delta_d*) is Dual_K(Hom_S(M,S)_d).
Its original quotient is dual to original coefficients phi(b(e_j)).
Original grading,entry degrees,negative zero pieces,coordinates and
kernel/cokernel comparisons are constructed,not assumed. Ordinary
homogeneous surjectivity produces exact-degree preimages. Mathlib's
original quotient/annihilator restriction equivalence proves the generic
vector coker(delta*) = Dual(ker delta) WITHOUT finite-dimensionality.
The categorical original-presentation specialization uses Type0 objects,
as in the manuscript;the underlying homogeneous kernel is universe generic.

GEOMETRY. Let S=K[x_sigma],sigma finite ordered,card(sigma)=n+2,
a_i,b_j natural,z_i=a_i+card(sigma),w_j=b_j+card(sigma).
Use the ACTUAL original homogeneous presentation c,b,R,E,M above,
with original scalar-compatible graded S-module structure on M.
On ORIGINAL Proj S and the ORIGINAL ordered coordinate basic-open cover,
H_Cech^(n+1)(native M(0)) is the ACTUAL coker of the previously verified
canonical polynomial dual matrix over Gamma(Spec K,O). Its entries come
from c(e_i)_j,not independent polynomials. Actual original free sheaf and
homology coordinate comparisons are constructed. Original quotient b
on actual top homology corresponds to the original polynomial matrix
quotient. Actual Noetherian presentation proves exactness/next-degree
vanishing;no abstract cokernel or cohomology square is an input.
This uses STATED natural free weights and degree zero,not arbitrary twists.

OPEN. Unify these prefixes by matching actual finite-sum/dual polynomial
coordinates and canonical K vs Gamma(Spec K,O) coefficient/scalar maps.
Arbitrary original integer-twist regrading,Koszul connecting/restriction
compatibility,uniform fixed-m section production and derived sheaf
cohomology comparison remain OPEN. Original4.1 normalized canonical
DUALIZING identification remains UNVERIFIED. Original4.1,4.2 and the
main theorem remain OPEN. No normality,smoothness or Cohen-Macaulay
hypothesis is added to original integral complex V.

9 root modules,663 physical root lines,36 exact root
declarations (19 proofs,17 definitions).
287 closed modules,278 older dependencies
match previous frozen source bytes. Exact root/transitive axioms only
propext,Classical.choice,Quot.sound. All compiles/audits use
lean_runner.run_file,one compiler,8GiB Windows Job,2threads,CPU<=25%,
20minutes. Old resource holds preserved. No whole-project rebuild or
whole-project Lean CI. Checkpoint180 remains last complete local
whole-project verification. Lean v4.35.0-rc3;mathlib
2a885768dae569d938bb9ff3474da6a8753bb90a. Original manuscript SHA256:
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Compile closed source in dependency order,then CheckAxioms.lean using the
same guarded runner. Linear.lean is the convenience entry. Reviewed
Apache2.0 source attribution retained;no downloaded setup script run.
