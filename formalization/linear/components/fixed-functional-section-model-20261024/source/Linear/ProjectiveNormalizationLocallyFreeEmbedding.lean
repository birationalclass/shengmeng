module
public import Linear.ProjectiveNormalizationNativeSheafEmbedding
public import Linear.ProjectiveNativePositiveTwist
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule

/-- The ORIGINAL finite normalization dual embeds into an ACTUAL
locally free quasicoherent positive twist on the original native Proj.
Local freeness is constructed from original coordinate charts, not
assumed as data. Identification with omega_V(r+1) remains separate. -/
theorem projectiveLinearNormalization_exists_native_locallyFree_embedding
    {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
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
    ∃ m : ℕ, 0 < m ∧ ∃ e : D →ₗ[B] B, Function.Injective e ∧
      ∃ hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+(m : ℤ)),
        Mono (nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE (m : ℤ) e hh 0) ∧
        (nativeProjectiveModuleSheaf 𝓑 ℰ hE (m : ℤ)).IsLocallyFree ∧
        (nativeProjectiveModuleSheaf 𝓑 ℰ hE (m : ℤ)).IsQuasicoherent := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  obtain ⟨m,hm,e,he,hh,hmono⟩ :=
    projectiveLinearNormalization_exists_native_sheaf_embedding V L hL hinj hfinite
  exact ⟨m,hm,e,he,hh,hmono,projectiveNativePositiveTwist_isLocallyFree V m,
    projectiveNativePositiveTwist_isQuasicoherent V m⟩

end LinearStudy
