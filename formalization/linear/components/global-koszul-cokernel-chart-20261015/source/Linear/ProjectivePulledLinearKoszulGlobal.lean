module
public import Linear.NativeProjectiveKoszulComplex
public import Linear.ProjectivePulledLinearKoszulForms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm projectivePulledLinearKoszulForms
  schemeModuleInternalHomCochainComplex

/-- ACTUAL original global Koszul complex K(H)(k) on ORIGINAL V, with
weights p*q. Its construction needs no finite-cut, exactness or CM certificate. -/
def projectivePulledLinearKoszulComplex (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1) (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    ChainComplex (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules ℕ := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact nativeProjectiveKoszulComplex (homogeneousQuotientPiece V.ideal.toIdeal)
    (projectivePulledLinearKoszulForms f V L w)
    (projectivePulledLinearKoszulForms_homogeneous f V L hL w) k

/-- The ACTUAL original global internal-Hom complex against ANY original
module sheaf N. This does not assert derived SHEAF Ext or the extension class. -/
def projectivePulledLinearKoszulInternalHom (f : HomogeneousEndomorphism n)
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1) (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules →
      CochainComplex (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules ℕ := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact fun N => schemeModuleInternalHomCochainComplex N
    (projectivePulledLinearKoszulComplex f V L hL w k)

end LinearStudy
