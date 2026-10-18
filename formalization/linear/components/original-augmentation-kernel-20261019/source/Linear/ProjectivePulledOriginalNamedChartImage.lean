module
public import Linear.ProjectivePulledOriginalNamedChartObjects
public import Linear.SchemeModuleChartImageHEq
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading projectivePulledOriginalNamedExactChart
variable {n r : ℕ}
/-- The actual named original chart has EXACT original X0-nonzero image.
Only pure chart objects/images are compared;no Ext or adjunction unit. -/
theorem projectivePulledOriginalNamedExactChart_image
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (w : Fin (r+1) → ℂ) (k : ℤ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let D := projectivePulledOriginalNamedExactChart f V L hL w k
    letI := D.2.2.1
    D.2.1 ''ᵁ ⊤ =
      Proj.basicOpen (homogeneousQuotientPiece V.ideal.toIdeal)
        (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let D := projectivePulledOriginalNamedExactChart f V L hL w k
  letI := D.2.2.1
  letI := projectivePulledOriginalAway_isOpenImmersion V
  let j := Proj.awayι (m := 1) (homogeneousQuotientPiece V.ideal.toIdeal)
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ one_pos
  have h := scheme_chart_image_top_eq_of_HEq
    (projectivePulledOriginalNamedExactChart f V L hL w k).2.1 j
    (projectivePulledOriginalNamedExactChart_ring f V L hL w k)
    (projectivePulledOriginalNamedExactChart_awayInclusion f V L hL w k)
  exact h.trans (j.image_top_eq_opensRange.trans
    (Proj.opensRange_awayι _ _ _ one_pos))
end LinearStudy
