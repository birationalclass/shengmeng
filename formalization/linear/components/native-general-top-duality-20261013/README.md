# Actual native Cech duality in every complementary degree

Let K be a field, sigma a finite ordered coordinate set with card(sigma)=n+2,
and m any natural number. Put P=Proj K[sigma], and use its actual native
integer twist T(-m-n-2) on the coordinate open cover. Put B=Gamma(Spec K,O).
Then the ACTUAL ordered Cech complex has a constructed isomorphism
H^(n+1)(Cech(P,T(-m-n-2))) ~= Hom_B(B[sigma]_m,B).
The right side is mathlib's ACTUAL homogeneous polynomial submodule dual.
This statement is for positive projective dimension, over any field.

Complementary weights e_i=-a_i-1 give an explicit equivalence between
all-negative Laurent weights and actual nonnegative monomial indices of
degree m. Reused mathlib bounded-degree finiteness proves this index finite.
The actual full-negative coefficient map is surjective, with kernel exactly
the actual boundary space. Its quotient isomorphism is composed with the
actual homogeneous monomial basis universal property. On each basis vector,
the resulting functional evaluates its complementary negative coefficient.
The actual native/Laurent complex isomorphism, including all differentials,
then transports this to mathlib's actual full-complex homology.

OPEN: compatibility with actual multiplication across twists and finite
graded presentations; derived sheaf cohomology comparison; actual Koszul
connecting maps and finite-scheme restriction compatibility. This is NOT
general proper duality and does not prove original4.2's section production.
Original4.1 canonical normalized-dualizing identification is UNVERIFIED.
Original4.1,original4.2 and main theorem remain OPEN. No condition on the
original complex integral V is added, and no whole-project checkpoint advances.

6 new modules, 436 physical source lines, 29 audited
declarations (11 proofs, 18 definitions).
Closed source contains 69 modules. All 63
older dependencies match previously frozen immutable source byte-for-byte.
Exact printed types and transitive axioms are included. Only propext,
Classical.choice and Quot.sound are permitted. All local compilation and
auditing used the single compiler resource controller, 8GiB Job hard limit,
2 threads, CPU25%, and 20-minute wall timeout. No whole-project checkpoint
or whole-project CI completion is claimed; checkpoint180 remains unchanged.

Online pinned official mathlib source was verified against the local cache
for finite homogeneous exponents, actual polynomial monomial bases and
linear basis construction/reindexing interfaces. The source provenance record is included. Earlier weight
assembly/contraction retains reviewed Apache2.0 AINTLIB attribution.

Pinned manuscript SHA256:
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Compile included modules in dependency order with the pinned toolchain and
lake-manifest, then CheckAxioms.lean. Linear.lean is a convenience entry.
