module
public import Linear.SchemeModuleChainSourceAcyclic
public import Linear.ProjectivePulledOriginalKoszulInternalExtVanishing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledLinearKoszulComplex
variable {n r : ℕ}

/-- Package ALREADY PROVED SAME original source acyclicity at exact named
Prop boundary,without passing desired unproved vanishings as hypotheses. -/
theorem projectivePulledOriginalKoszul_sourceExtAcyclic
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ)
    (N : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    schemeModuleChainSourceExtAcyclic (projectivePulledLinearKoszulComplex f V L hL w k) N := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  intro p j
  exact projectivePulledOriginalKoszulInternalExt_succ f V L hL w k p N j

end LinearStudy
