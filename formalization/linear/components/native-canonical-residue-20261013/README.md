# Actual native canonical-twist top Cech residue

Let K be a field, and sigma a finite ordered coordinate set with
card(sigma)=n+2. Let P be the actual projective scheme Proj K[sigma],
with its actual coordinate open cover and native integer twist T(-n-2).
Then the top cohomology in degree n+1 of the ACTUAL ordered Cech complex
is isomorphic, as a module, to Gamma(Spec K,O).

The isomorphism is constructed from the Laurent coefficient of the weight
(-1,...,-1). Every other weight of degree -card(sigma) has a coordinate
outside its negative support and admits the previously proved contraction.
Finite weight reconstruction proves that the residue kernel is exactly
the image of the actual previous differential. The full-support weight
has zero previous term and one top coordinate. This proves residue
surjectivity and vanishing on boundaries. The actual native/Laurent
comparison transfers these identities, and pinned mathlib's quotient and
ShortComplex homology APIs give the actual full-complex homology isomorphism.
No residue, contraction-exactness, or duality certificate is a hypothesis.

This is Cech homology, NOT a proved comparison with derived sheaf
cohomology, general Serre duality, or proper duality. Original4.1 canonical
normalized-dualizing identification is still UNVERIFIED. Original4.2 needs
general twisted duality, actual Koszul section production and compatibility
with restriction to its finite scheme. Original4.1/4.2 and the main theorem
remain OPEN. This component imposes no new condition on the original V.

8 new modules, 599 physical source lines, 42 audited
declarations (25 proofs, 17 definitions).
Closed source contains 66 modules. All 58
older dependencies match previously frozen immutable source byte-for-byte.
Exact printed types and transitive axioms are included. Only propext,
Classical.choice and Quot.sound are permitted. All local compilation and
auditing used the single compiler resource controller, 8GiB Job hard limit,
2 threads, CPU25%, and 20-minute wall timeout. No whole-project checkpoint
or whole-project CI completion is claimed; checkpoint180 remains unchanged.

Online pinned official mathlib source was verified against the local cache
for finite-order enumerations, quotient isomorphisms and actual homology
interfaces. The source provenance record is included. Earlier weight
assembly/contraction retains reviewed Apache2.0 AINTLIB attribution.

Pinned manuscript SHA256:
503864b699ae2b315ff857a57f33fb1d722ab53f331040ae6afafcd2e691ef2a.
Compile included modules in dependency order with the pinned toolchain and
lake-manifest, then CheckAxioms.lean. Linear.lean is a convenience entry.
