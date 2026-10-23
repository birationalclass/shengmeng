module
public import Linear.ProjectiveNormalizationLocallyFreeEmbedding
public import Linear.HomogeneousEmbeddingAboveBound
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule

/-- The ORIGINAL finite normalization dual has a constructed actual native
sheaf monomorphism into a positive locally free twist ABOVE any prescribed
bound. Neither the higher embedding nor its comparison is supplied as data.
The canonical/normalized-dualizing identification remains separate. -/
theorem projectiveLinearNormalization_exists_native_embedding_above
    {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (lower : ℕ) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let ℰ := nativeProjectiveRingIntegerPiece 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    let hE := nativeProjectiveRingIntegerPiece_graded 𝓑
    ∃ m : ℕ, lower ≤ m ∧ 0 < m ∧ ∃ e : D →ₗ[B] B, Function.Injective e ∧
      ∃ hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+(m : ℤ)),
        Mono (nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE (m : ℤ) e hh 0) ∧
        (nativeProjectiveModuleSheaf 𝓑 ℰ hE (m : ℤ)).IsLocallyFree ∧
        (nativeProjectiveModuleSheaf 𝓑 ℰ hE (m : ℤ)).IsQuasicoherent := by
  letI := V.prime
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let ℰ := nativeProjectiveRingIntegerPiece 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let hE := nativeProjectiveRingIntegerPiece_graded 𝓑
  obtain ⟨k,hk,e₀,he₀,hhom₀⟩ :=
    projectiveLinearNormalization_exists_homogeneous_dual_embedding V L hL hinj hfinite
  have hb : φ (MvPolynomial.X (0 : Fin (r+1))) ∈ 𝓑 1 := by
    apply (homogeneousQuotientPiece_mem_iff _ _ _).mpr
    refine ⟨L 0,hL 0,?_⟩
    simp only [φ,projectiveLinearNormalizationMap,AlgHom.comp_apply,MvPolynomial.aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
  have hne : φ (MvPolynomial.X (0 : Fin (r+1))) ≠ 0 := by
    intro hz
    apply MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (r+1))
    apply hinj
    simpa only [map_zero] using hz
  obtain ⟨m,hbound,hm,e,he,hhom⟩ := homogeneous_embedding_exists_shift_above
    𝓑 𝒟 (k : ℤ) e₀ he₀ hhom₀ (φ (MvPolynomial.X (0 : Fin (r+1)))) hb hne lower
  have hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+(m : ℤ)) := by
    intro d ell hell
    exact nativeProjectiveRingIntegerPiece_mem_of_projection 𝓑 (d+(m : ℤ)) (e ell)
      (hhom d ell hell)
  exact ⟨m,hbound,hm,e,he,hh,
    nativeProjectiveModuleSheafMap_mono 𝓑 𝒟 ℰ hD hE (m : ℤ) e hh he 0,
    projectiveNativePositiveTwist_isLocallyFree V m,
    projectiveNativePositiveTwist_isQuasicoherent V m⟩
end LinearStudy
