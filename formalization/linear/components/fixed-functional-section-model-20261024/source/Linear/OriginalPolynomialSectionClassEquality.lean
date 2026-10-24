module
public import Linear.OriginalProjectivePolynomialSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
/-- ANY two original homogeneous polynomials of the same degree and
same original quotient class have the SAME actual polynomial section. -/
theorem originalProjectivePolynomialSection_eq_of_quotient_eq
    {n : ℕ} (V : IntegralProjectiveEquations n) (m : ℕ)
    (Q : CoordinateRing n) (hQ : Q.IsHomogeneous m)
    (Q' : CoordinateRing n) (hQ' : Q'.IsHomogeneous m)
    (h : Ideal.Quotient.mk V.ideal.toIdeal Q=Ideal.Quotient.mk V.ideal.toIdeal Q') :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    originalProjectivePolynomialSection V m Q hQ=originalProjectivePolynomialSection V m Q' hQ' := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  apply Subtype.ext
  funext p
  change LocalizedModule.mk (Ideal.Quotient.mk V.ideal.toIdeal Q) 1 =
    LocalizedModule.mk (Ideal.Quotient.mk V.ideal.toIdeal Q') 1
  rw [h]
end LinearStudy
