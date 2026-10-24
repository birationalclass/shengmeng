module
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
/-- Project the exact polynomial-image fields from the FULL actual
section-image predicate;this is a theorem about the exposed definition. -/
theorem originalGradedPolynomialSectionImageStatement_polynomial_images
    (m : ℕ) (e : D →ₗ[CoordinateRing n ⧸ V.ideal.toIdeal] (CoordinateRing n ⧸ V.ideal.toIdeal))
    (j : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      let B := homogeneousQuotientPiece V.ideal.toIdeal
      nativeProjectiveModuleSheaf B DG hD 0 ⟶
        nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
          (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ))
    (hImage : originalGradedPolynomialSectionImageStatement V DG hD m e j) :
    ∀ z : D,z ∈ DG 0 → z ≠ 0 →
      ∃ Q : CoordinateRing n,Q.IsHomogeneous m ∧ Q ∉ V.ideal.toIdeal ∧
        Ideal.Quotient.mk V.ideal.toIdeal Q=e z := by
  unfold originalGradedPolynomialSectionImageStatement at hImage
  intro z hz hne
  obtain ⟨Q,hQ,hnot,hval,_⟩ := hImage z hz hne
  exact ⟨Q,hQ,hnot,hval⟩
end LinearStudy
