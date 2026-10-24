module
public import Linear.OriginalProjectivePolynomialSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The ORIGINAL polynomial section is the SAME element/1 section of its
specified quotient image. Equality of quotient elements is proved data;
no independent section comparison is assumed. -/
theorem originalProjectivePolynomialSection_eq_of_quotient_image
    {n : ℕ} (V : IntegralProjectiveEquations n) (m : ℕ)
    (Q : CoordinateRing n) (hQ : Q.IsHomogeneous m)
    (x : CoordinateRing n ⧸ V.ideal.toIdeal)
    (hx : x ∈ nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal) (m:ℤ))
    (h : Ideal.Quotient.mk V.ideal.toIdeal Q=x) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    originalProjectivePolynomialSection V m Q hQ =
      nativeProjectiveModuleHomogeneousGlobalSection B (nativeProjectiveRingIntegerPiece B)
        (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ) ⟨x,hx⟩ := by
  subst x
  rfl
end LinearStudy
