module
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
/-- FULL section-image predicate;STATEMENT only,not a proof. -/
def originalGradedPolynomialSectionImageStatement
    (m : ℕ) (e : D →ₗ[CoordinateRing n ⧸ V.ideal.toIdeal] (CoordinateRing n ⧸ V.ideal.toIdeal))
    (j : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      let B := homogeneousQuotientPiece V.ideal.toIdeal
      nativeProjectiveModuleSheaf B DG hD 0 ⟶
        nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
          (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ)) : Prop :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  ∀ (z : D) (hz : z ∈ DG 0),z ≠ 0 →
    ∃ (Q : CoordinateRing n) (hQ : Q.IsHomogeneous m),Q ∉ V.ideal.toIdeal ∧
      Ideal.Quotient.mk V.ideal.toIdeal Q=e z ∧
      (j.app ⊤) (nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ⟨z,hz⟩) =
        originalProjectivePolynomialSection V m Q hQ ∧
      originalProjectivePolynomialSection V m Q hQ ≠ 0 ∧
      nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ⟨z,hz⟩ ≠ 0

/-- Generic ORIGINAL-V image step,abstracted in the source module to avoid
repeated coextension type expansion. All polynomial/section conclusions
are exposed in the preceding statement definition. -/
theorem originalGradedPolynomialSectionImageStatement_of_formula
    (m : ℕ) (e : D →ₗ[CoordinateRing n ⧸ V.ideal.toIdeal] (CoordinateRing n ⧸ V.ideal.toIdeal))
    (j : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      let B := homogeneousQuotientPiece V.ideal.toIdeal
      nativeProjectiveModuleSheaf B DG hD 0 ⟶
        nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
          (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ))
    (hj : Mono j)
    (he : Function.Injective e)
    (hh : ∀ d : ℤ,∀ z : D,z ∈ DG d → e z ∈
      nativeProjectiveRingIntegerPiece (homogeneousQuotientPiece V.ideal.toIdeal) (d+(m:ℤ)))
    (hformula : letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
      let B := homogeneousQuotientPiece V.ideal.toIdeal
      ∀ z : DG 0,(j.app ⊤) (nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 z) =
        nativeProjectiveModuleHomogeneousGlobalSection B (nativeProjectiveRingIntegerPiece B)
          (nativeProjectiveRingIntegerPiece_graded B) (m:ℤ)
          ⟨e (z:D),by simpa only [zero_add] using hh 0 z z.property⟩)
    {r : ℕ} (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L)) :
    originalGradedPolynomialSectionImageStatement V DG hD m e j := by
  unfold originalGradedPolynomialSectionImageStatement
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  let EG := nativeProjectiveRingIntegerPiece B
  let hE := nativeProjectiveRingIntegerPiece_graded B
  intro B0 z hz hne
  have himage : e z ∈ B m := by
    simpa only [zero_add,nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,if_true,
      Int.toNat_natCast] using hh 0 z hz
  have hp : ∃ Q : CoordinateRing n,Q.IsHomogeneous m ∧ Q ∉ V.ideal.toIdeal ∧
      Ideal.Quotient.mk V.ideal.toIdeal Q=e z :=
    originalPolynomial_exists_of_injective_image (n:=n) (D:=D) V e he m z hne himage
  obtain ⟨Q,hQ,hQnot,hval⟩ := hp
  have hvalue : (j.app ⊤)
      (nativeProjectiveModuleHomogeneousGlobalSection B DG hD 0 ⟨z,hz⟩) =
      originalProjectivePolynomialSection V m Q hQ := by
    exact (hformula ⟨z,hz⟩).trans
      (originalProjectivePolynomialSection_eq_of_quotient_image V m Q hQ (e z)
        (by simpa only [zero_add] using hh 0 z hz) hval).symm
  have hsection : originalProjectivePolynomialSection V m Q hQ ≠ 0 :=
    originalProjectivePolynomialSection_nonzero_of_normalization (n:=n) (r:=r) V L hL hinj m Q hQ hQnot
  refine ⟨Q,hQ,hQnot,hval,hvalue,hsection,?_⟩
  letI : Mono j := hj
  exact (moduleSheafMono_section_ne_zero_iff j ⊤ _).mp (hvalue.symm ▸ hsection)
end LinearStudy
