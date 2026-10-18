module
public import Linear.ProjectivePulledOriginalNamedExactChart
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading
variable {n r : ℕ}
variable (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
variable (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
variable (w : Fin (r+1) → ℂ) (k : ℤ)
/-- Exact original named chart ring,proved independently of Ext or source isos. -/
theorem projectivePulledOriginalNamedExactChart_ring :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (projectivePulledOriginalNamedExactChart f V L hL w k).1 =
      CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact Eq.refl ((projectivePulledOriginalNamedExactChart f V L hL w k).1)
/-- Exact SAME original away inclusion,without a dependent-package cast. -/
theorem projectivePulledOriginalNamedExactChart_inclusion :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    HEq (projectivePulledOriginalNamedExactChart f V L hL w k).2.1
      (originalProjectiveZeroChart V) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact HEq.refl ((projectivePulledOriginalNamedExactChart f V L hL w k).2.1)
/-- SAME original native away inclusion,with literal native syntax. -/
theorem projectivePulledOriginalNamedExactChart_awayInclusion :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    HEq (projectivePulledOriginalNamedExactChart f V L hL w k).2.1
      (Proj.awayι (m := 1) (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
        ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ one_pos) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact HEq.refl ((projectivePulledOriginalNamedExactChart f V L hL w k).2.1)
/-- The literal original native away inclusion is an open immersion. -/
theorem projectivePulledOriginalAway_isOpenImmersion :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsOpenImmersion (Proj.awayι (m := 1) (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
      ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ one_pos) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  dsimp only [Proj.awayι]
  exact IsOpenImmersion.comp _ _
end LinearStudy
