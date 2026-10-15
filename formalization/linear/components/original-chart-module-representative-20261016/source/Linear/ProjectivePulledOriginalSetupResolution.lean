module
public import Linear.ChosenProjectiveNormalizationDimensions
public import Linear.ProjectivePulledWholeCutNativeTwistQuotientAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- ACTUAL original-Setup proof value:derive the formerly explicit
nonzero defining ideal and affine dimension FROM THE SAME chosen original
finite injective normalization and original r<n. Then derive ONE NONEMPTY
parameter open BEFORE ALL integer twists with actual WHOLE-cut native
quotient-induced augmentation and its quasi-isomorphism. Neither source
exactness,dimension,nonzero ideal nor target comparison is a new premise.
Original epsilon/connecting boundary and local support remain separate. -/
def projectivePulledLinearSectionOriginalSetupResolutionProof
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n) (hrn : r < n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (x0 : Fin n → ℂ) (hx0 : normalizedProjectivePoint x0 ∈ V.zeroSet) :=
  projectivePulledLinearSection_exists_wholeCutNativeTwist_quotientAugmentation_quasiIso
    f V (chosenProjectiveNormalization_definingIdeal_ne_bot V L hinj hfinite hrn)
    hq hf hV L hL hinj hfinite
    (chosenProjectiveNormalization_chart_dimension V L hinj hfinite x0 hx0) x0 hx0

end LinearStudy
