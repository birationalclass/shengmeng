module
public import Linear.ProjectivePulledOriginalKoszulInternalExtVanishing
public import Linear.NativeKoszulFiniteTopTerm
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf projectivePulledLinearKoszulForms
variable {n r : ℕ}

/-- Actual SAME ORIGINAL named Koszul source is zero ABOVE its original
rank,using the original exterior basis. No boundedness certificate input. -/
theorem projectivePulledOriginalKoszul_isZero_above
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) (p : ℕ) (hp : r < p) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsZero ((projectivePulledLinearKoszulComplex f V L hL w k).X p) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  change IsZero ((nativeProjectiveKoszulComplex (homogeneousQuotientPiece V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k).X p)
  rw [nativeProjectiveKoszulComplex_X]
  exact nativeProjectiveKoszulTerm_isZero_above_rank _ r f.degree p k hp

end LinearStudy
