module
public import Linear.ProjectivePulledLinearKoszulGlobal
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The ACTUAL original X0 chart; retain the original homogeneous quotient
and the native Proj.away inclusion. This is constructed data,not a proof. -/
def originalProjectiveZeroChart (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Spec (CommRingCat.of (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
      (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0)))) ⟶
      Proj (homogeneousQuotientPiece V.ideal.toIdeal) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact Proj.awayι (m := 1) (homogeneousQuotientPiece V.ideal.toIdeal)
    (Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X 0))
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X ℂ 0,rfl⟩ one_pos

/-- The named original X0 chart IS an open immersion. Its native basic-open
isomorphism and inclusion establish the property; it is not a premise. -/
theorem originalProjectiveZeroChart_isOpenImmersion (V : IntegralProjectiveEquations n) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsOpenImmersion (originalProjectiveZeroChart V) := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  dsimp only [originalProjectiveZeroChart,Proj.awayι]
  exact IsOpenImmersion.comp _ _

end LinearStudy