# General polynomial transpose on actual native top Cech homology

Let K be a field, sigma a finite ordered coordinate set of cardinality
r+1, r>=1, and l,m>=0. Let P=Proj K[sigma], T(k) its original integer
twist defined by locally homogeneous fractions, and p ANY actual
degree-l homogeneous polynomial. Let B=Gamma(Spec K,O) and Phi:K->B
the canonical inverse of the actual GammaSpec ring isomorphism.
Then ORIGINAL sheaf multiplication
M_p:T(-(l+m)-r-1)->T(-m-r-1), passed through the original Cech functor,
is transpose to ACTUAL homogeneous polynomial multiplication
mu_(Phi p):S_m(B)->S_(l+m)(B) under the verified native top Cech duality:
D_m o H_Cech^r(M_p) = mu_(Phi p)^dual o D_(l+m).

The proof first checks every original monomial coefficient kappa, with
its actual Phi(kappa) coefficient on every coordinate intersection.
Actual native sheaf multiplication is additive in p. Original homology
maps preserve finite sums; the required scalar compatibility, absent
as an implemented homologyMap_smul in the pinned mathlib, is proved
from actual boundary quotient maps. Its outgoing-zero premises are
actually verified on the original top complex. The actual homogeneous
polynomial coefficient map is semilinear. mathlib monomial bases give
the finite expansion of p, while actual multiplication and its linear
transpose give the matching polynomial-side sum.
No multiplication or homology map is defined by duality coordinates.
The only integer-degree transports are genuine proved equalities.

This completes general homogeneous polynomial naturality for actual
native top Cech homology. It does NOT establish derived sheaf cohomology
comparison, finite graded-presentation duality or actual Koszul
connecting-map/restriction compatibility. Original4.1 canonical
normalized-dualizing identification stays UNVERIFIED;original4.1/4.2
and the main theorem remain OPEN, with all original hypotheses and
numbering preserved. No normality,smoothness or Cohen-Macaulay condition
is added to the original integral V.

11 new modules;678 physical source lines;34 audited
declarations (26 proofs and 8 definitions).
123 closed modules;112 older dependencies
match previously frozen bytes. Exact types and transitive axioms are
included:only propext,Classical.choice,Quot.sound. Every compile and
audit uses lean_runner.run_file,one compiler,8GiB Job memory,2threads,
CPU<=25%,20minutes. No whole-project checkpoint/Lean CI is asserted.

Pinned Lean v4.35.0-rc3;mathlib2a885768dae569d938bb9ff3474da6a8753bb90a.
Original manuscript SHA256:
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Compile closed modules in dependency order,then CheckAxioms.lean.
Linear.lean is the convenience entry. Previous Apache2.0 attribution
is preserved. No downloaded setup program is executed.
