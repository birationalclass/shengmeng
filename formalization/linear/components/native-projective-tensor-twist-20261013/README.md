# Original Lemma4.2: actual native tensor twist comparison

Original Lemma4.1/4.2 and the Linearity Theorem remain OPEN. The genuine
canonical/normalized-dualizing identification remains UNVERIFIED. Original
hypotheses, manuscript numbering and one fixed m before all iterates are unchanged.

Let K be a field, S a commutative graded K-algebra, and M an actual S-module
with K-linear pieces M_d for d in Z. Assume S_n M_d is contained in M_(n+d).
The internal direct-sum decomposition of M is not needed for this comparison.
Let a_i lie in S_1 and algebraically generate S over K, m in N and k in Z.
Then the ACTUAL native local-fraction sheaves satisfy

  T_m(S) tensor T_k(M) ~= T_(k+m)(M).

The tensor is the actual sectionwise tensor presheaf followed by mathlib's
module-sheafification. The isomorphism is constructed from actual localized
ring/module multiplication and the module-sheafification adjunction. Its
universal presheaf map is proved to be the original bilinear fraction pairing.
No isomorphism, local-bijection, finite-generation, freeness or Noetherian
certificate is supplied. Degree-one algebra generators imply the actual
native Proj chart cover, and all restriction maps are the original ones.

On every original open where a is nonzero, the twist map is multiplication
by a^m. The actual inverse sends ell/b to ell/(b*a^m). The ring frame and
module frame give a proved sectionwise tensor linear equivalence. This proves
local injectivity and surjectivity on the original site; module-sheafification
turns the actual multiplication into the constructed global isomorphism.

Minimal library reuse: mathlib LinearMap.lsmul, localized modules, tensor
presheaves and module-sheafification; the 20-line local-bijection criterion
is minimally adapted from CBirkbeck/AINTLIB SheafOfModulesMonoidal.lean,
commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17. Its Apache2.0 copyright
and attribution are preserved. No other foreign closure is imported.
Two actual generic adjunction calculations resolve the Hom-equivalence
interface; actual target objects are specified instead of relying on
expensive reverse inference from a forgotten presheaf.

The EXTERNAL Serre pole/tensor-power model comparison remains OPEN, as do
the original ideal-sheaf comparison, uniform eventual H1 vanishing independent
of q, ambient homogeneous polynomial/global-section comparison and lifting,
and Koszul/proper-duality production of the nonzero section. This is a native
tensor comparison; it does not prove any of those missing statements.

Fourteen new canonical LF modules, 1034 physical source lines,28 proofs,
13 definitions and41 exact type/standard-axiom audits. The110-module closed
source has96 dependencies byte-identical to checkpoint180. All imported
project-owned sources are included. Compiler/resource logs and exact types
are included. Only propext,Classical.choice and Quot.sound occur. One compiler,
8GiB hard Windows Job,2 threads,CPU25%,below normal,20-minute timeout.
Failed or deterministic-timeout drafts are retained privately, not counted.
Linear.lean is a reproducibility import entry, not separately compiled.
Whole-project checkpoint180 and full-project Lean CI are unchanged.
