# Original Lemma4.2: actual native projective H1-to-section lifting

Original Lemma4.1/4.2 and the Linearity Theorem remain OPEN. The genuine
canonical identification remains UNVERIFIED. Original hypotheses, numbering
and one fixed m before all iterates are preserved.

Let X be an actual scheme. Its actual underlying-additive-sheaf functor
preserves finite limits, colimits and zero maps; actual short exact sequences
are proved preserved. This minimally adapts CBirkbeck/AINTLIB SchemeModuleSheaf
at ab1451487da02cd4483d0e2cdb2cc9e44bbbac17, Apache2.0, using Linear's fixed
mathlib2a885768dae569d938bb9ff3474da6a8753bb90a. No foreign whole-library
import or exactness-comparison certificate is assumed.

Let 0 -> A -> B -> C -> 0 be an ACTUAL short exact sequence of O_X-modules.
Assume genuine mathlib H1 of the underlying additive A is zero.
Then B(X) -> C(X) is surjective. For an actual module-sheaf epimorphism f,
the kernel short exact sequence is constructed. Thus H1(ker f)=0 implies
section surjectivity without assuming a section-lifting certificate.

Let e:D -> E be an ACTUAL surjective homogeneous graded-module map and fix
an integer k. Homogeneous surjectivity derives an epimorphism of ACTUAL
native local-fraction sheaves on the SAME Proj in the SAME degree k.
If H1 of the ACTUAL kernel of that sheaf map vanishes, EVERY actual global
section of its target lifts. Graded-to-sheaf and kernel exactness are derived.

H1 vanishing is an EXPLICIT PREMISE, not proved eventual Serre vanishing.
The actual I_V(m), native-twist/Serre-line-bundle comparison, eventual
vanishing in ONE degree independent of q, ambient polynomial/global-section
comparison and Koszul/proper-duality nonzero-section production remain OPEN.
Do not use this conditional implication to claim the original lemma proved.

Four new canonical LF modules:9 proofs,1 definition,10 exact type/axiom
audits. The21-module source closure has16 byte-identical checkpoint180
dependencies and1 byte-identical dependency from the preceding verified
component.199 new physical lines include comments and blanks. All compiler,
resource and exact type/axiom logs are included. Only propext,Classical.choice
and Quot.sound occur. One compiler,8GiB hard Windows Job,two threads,CPU25%,
below normal,20-minute timeout. Largest accepted root compile4.11GiB;
accepted audit4.09GiB. No resource-interrupted or partial job counted.
Linear.lean is a reproducibility import entry, not separately compiled.
This is an independent local component, not a full-project checkpoint or CI.
The latest complete local checkpoint remains180.
