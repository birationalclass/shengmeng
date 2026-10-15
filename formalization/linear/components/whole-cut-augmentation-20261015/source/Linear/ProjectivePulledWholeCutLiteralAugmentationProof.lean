module
public import Linear.ProjectivePulledOriginalQuotientAugmentationProof
public import Linear.ProjectivePulledWholeCutLiteralTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulForms
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm nativeProjectiveKoszulMappedPresentationData
  projectivePulledKoszulWholeCutLiteralTargetIso CategoryTheory.Functor.mapHomologicalComplex
variable {n r : ℕ}

/-- Apply the target-parametric ORIGINAL projection proof to the separately
constructed LITERAL-quotient/WHOLE-cut native-twist target comparison.
This proves the actual global chain augmentation and chart-adjoint
formula; no target comparison or desired map formula is an assumption.
The two cover conditions are derived in the original family theorem.
A separately defined canonical geometric quotient map is not identified here. -/
def projectivePulledWholeCutLiteralAugmentationProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (hc : projectivePulledWholeCutNativeAugmentationConditions f V L hL w) :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  projectivePulledLinearKoszulOriginalQuotientAugmentationProof f V L hL w k hc.1 _
    (projectivePulledKoszulWholeCutLiteralTargetIso f V L hL w k hc.2)

end LinearStudy
