module
public import Linear.OriginalPolynomialSectionImageProjections
public import Linear.OriginalGradedPolynomialSectionImage
public import Linear.OriginalPolynomialSectionClassEquality
public import Linear.NativeHomogeneousEmbeddingSectionFormula
public import Linear.SheafEmbeddingSectionTransport
public import Linear.OriginalPolynomialSectionNonzero
public import Linear.OriginalPolynomialSectionImageEquality
public import Linear.OriginalPolynomialInjectiveImageLift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} (V : IntegralProjectiveEquations n)
variable {D : Type} [AddCommGroup D]
variable [Module (CoordinateRing n ⧸ V.ideal.toIdeal) D] [Module ℂ D]
variable (DG : ℤ → Submodule ℂ D)
variable (hD : ∀ a : ℕ,∀ d : ℤ,∀ b : CoordinateRing n ⧸ V.ideal.toIdeal,
  b ∈ homogeneousQuotientPiece V.ideal.toIdeal a →
  ∀ z : D,z ∈ DG d → b • z ∈ DG ((a:ℤ)+d))
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveModuleSheaf originalProjectivePolynomialSection
/-- The SAME actual embedding formula holds for ANY retained Q with the
same original quotient image,not just a fresh existential polynomial. -/
theorem originalGradedPolynomialSectionImageStatement_any_polynomial
    (m : ℕ) (e : D →ₗ[CoordinateRing n ⧸ V.ideal.toIdeal] (CoordinateRing n ⧸ V.ideal.toIdeal))
    (j : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      let B := homogeneousQuotientPiece V.ideal.toIdeal
      nativeProjectiveModuleSheaf B DG hD 0 ⟶
        nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
          (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ))
    (hImage : originalGradedPolynomialSectionImageStatement V DG hD m e j)
    (z : D) (hz : z ∈ DG 0) (hne : z ≠ 0)
    (Q : CoordinateRing n) (hQ : Q.IsHomogeneous m)
    (hval : Ideal.Quotient.mk V.ideal.toIdeal Q=e z) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    (j.app ⊤) (nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ⟨z,hz⟩) =
      originalProjectivePolynomialSection V m Q hQ ∧
    originalProjectivePolynomialSection V m Q hQ ≠ 0 ∧
    nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ⟨z,hz⟩ ≠ 0 := by
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  unfold originalGradedPolynomialSectionImageStatement at hImage
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  have hData : ∃ (Q0 : CoordinateRing n) (hQ0 : Q0.IsHomogeneous m),Q0 ∉ V.ideal.toIdeal ∧
      Ideal.Quotient.mk V.ideal.toIdeal Q0=e z ∧
      (j.app ⊤) (nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ⟨z,hz⟩) =
        originalProjectivePolynomialSection V m Q0 hQ0 ∧
      originalProjectivePolynomialSection V m Q0 hQ0 ≠ 0 ∧
      nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ⟨z,hz⟩ ≠ 0 :=
    hImage z hz hne
  obtain ⟨Q0,hQ0,hnot0,hval0,hj0,hs0,hz0⟩ := hData
  have hEq : originalProjectivePolynomialSection V m Q0 hQ0 =
      originalProjectivePolynomialSection V m Q hQ :=
    originalProjectivePolynomialSection_eq_of_quotient_eq
    (n:=n) V m Q0 hQ0 Q hQ (hval0.trans hval.symm)
  exact ⟨hj0.trans hEq,hEq ▸ hs0,hz0⟩
end LinearStudy
