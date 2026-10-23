module
public import Linear.OriginalProjectivePolynomialSection
public import Linear.ProjectiveNormalizationGradedDual
public import Linear.NativeProjectiveChartSectionsInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
/-- For ORIGINAL V,a nonzero quotient polynomial class gives a NONZERO
ACTUAL original polynomial section. A genuine Proj point is CONSTRUCTED
from a nonzero positive-degree normalization coordinate,using the existing
generic chart point and torsion-free localization theorem. Nonempty Proj
and localization injectivity are not new hypotheses. -/
theorem originalProjectivePolynomialSection_nonzero_of_normalization
    {n r : ℕ} (V : IntegralProjectiveEquations n)
    (P : Fin (r+1) → CoordinateRing n) (hP : ∀ i,(P i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V P))
    (m : ℕ) (Q : CoordinateRing n) (hQ : Q.IsHomogeneous m) (hQnot : Q ∉ V.ideal.toIdeal) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    originalProjectivePolynomialSection V m Q hQ ≠ 0 := by
  letI : V.ideal.toIdeal.IsPrime := V.prime
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  let b : S := projectiveLinearNormalizationMap V P (MvPolynomial.X (0:Fin (r+1)))
  have hb : b ∈ B 1 := by
    apply (homogeneousQuotientPiece_mem_iff _ _ _).mpr
    refine ⟨P 0,hP 0,?_⟩
    simp only [b,projectiveLinearNormalizationMap,AlgHom.comp_apply,MvPolynomial.aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
  have hbn : b ≠ 0 := by
    intro hz
    apply MvPolynomial.X_ne_zero (R:=ℂ) (0:Fin (r+1))
    apply hinj
    simpa only [map_zero] using hz
  let p := (nativeProjectiveGenericChartPoint B 1 one_pos b hb hbn).1
  let ell : nativeProjectiveRingIntegerPiece B (m:ℤ) :=
    ⟨Ideal.Quotient.mk V.ideal.toIdeal Q,by
      simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,if_true,
        Int.toNat_natCast] using (show Ideal.Quotient.mk V.ideal.toIdeal Q ∈ B m from ⟨Q,hQ,rfl⟩)⟩
  intro hs
  have hs0 : nativeProjectiveModuleHomogeneousGlobalSection B
      (nativeProjectiveRingIntegerPiece B) (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ) ell=0 := hs
  have hzero := (nativeProjectiveModuleHomogeneousGlobalSection_eq_zero_iff_of_point B
    (nativeProjectiveRingIntegerPiece B) (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ) ell p).mp hs0
  exact hQnot (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
end LinearStudy
