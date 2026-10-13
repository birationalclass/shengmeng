module
public import Linear.OriginalNormalizationNativeObjects
public import Linear.ProjectiveNormalizationEmbeddingAboveBound
public import Linear.NativeDegreeZeroEmbeddingTarget
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule

/-- Construct the ACTUAL original normalization-dual embedding above the
given bound with compact original object names. The original homogeneous
map, its injection and the target equality are all proved constructions. -/
theorem originalNormalizationNativeDual_exists_embedding_above
    {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (lower : ℕ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧
      ∃ j : originalNormalizationNativeDualSheaf V L hL ⟶ originalProjectiveNativeTwist V m,
        Mono j ∧ (originalProjectiveNativeTwist V m).IsLocallyFree ∧
          (originalProjectiveNativeTwist V m).IsQuasicoherent := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let ℰ := nativeProjectiveRingIntegerPiece 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let hE := nativeProjectiveRingIntegerPiece_graded 𝓑
  obtain ⟨m,hbound,hm,e,he,hh,hmono,hfree,hqc⟩ :=
    projectiveLinearNormalization_exists_native_embedding_above V L hL hinj hfinite lower
  obtain ⟨j,hj⟩ := nativeProjectiveHomogeneousInjection_exists_zero_degree_mono
    𝓑 𝒟 ℰ hD hE (m : ℤ) e hh he
  refine ⟨m,hbound,hm,?_,?_,?_,?_⟩
  · exact j
  · exact hj
  · exact hfree
  · exact hqc
end LinearStudy
