# Native original Proj chart comparison

Online discovery: official mathlib4 documentation for
https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.html
and ProjectiveSpectrum Scheme/Topology; original mathlib4 repository searches
for homogeneous localization and quotient/dehomogenization. The native Proj
open-to-Spec theorem applies to any homogeneous element of positive degree.
It does not by itself identify our original dehomogenized coordinate quotient
with its HomogeneousLocalization.Away ring. No matching ready-made quotient
comparison was found in this focused discovery; this is not a claim of universal absence.

Read exact pinned source at mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a:
- RingTheory/GradedAlgebra/HomogeneousLocalization.lean: Away.mk_surjective,
  val_injective, actual homogeneous numerator/denominator construction;
- AlgebraicGeometry/ProjectiveSpectrum/Basic.lean: Proj.basicOpenIsoSpec;
- RingTheory/MvPolynomial/Homogeneous.lean: exact homogeneous C/X types;
- native localization universal properties and RingEquiv.subringCongr.

Reuse existing checked project constructions: homogeneousQuotientGrading,
projectiveChartCoordinateEmbedding, its exact original affine-ideal kernel,
coordinateRatioPolynomialMap_homogeneous and awayFractionEmbedding.

New uncovered bridge: identify both rings by their SAME actual image in the
original cone fraction field. Native homogeneous fractions map to normalized
homogeneous polynomial evaluations. Conversely constants and all actual
coordinate ratios lie in the native image, giving equality for the whole
affine quotient. Injective maps and equal images yield a ring isomorphism;
the pinned Proj basic-open theorem gives the actual open-subscheme isomorphism.

Scope: the original inhabited first-coordinate chart, over complex numbers.
No all-chart gluing, original f global scheme map, pullback transversality,
geometric Koszul, fixed-degree Q or final intersection proof is asserted.
Private successful build and standard-axiom outputs are preserved in
log-native-projective-chart6.log; public proof excludes diagnostic #print lines.
