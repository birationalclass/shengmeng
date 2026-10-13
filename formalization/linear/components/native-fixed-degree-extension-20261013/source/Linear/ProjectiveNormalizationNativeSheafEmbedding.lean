module
public import Linear.CoextensionProjectiveGradeCompatibility
public import Linear.ProjectiveNormalizationHomogeneousEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
variable {n r : ℕ}

/-- The ORIGINAL normalization dual gives an actual global monomorphism
of native Proj module sheaves into the actual homogeneous ring's
degree-m local-fraction sheaf, with ONE positive m. No sheaf model,
canonical comparison, or global-morphism certificate is supplied.
Identifying the source with the canonical sheaf remains separate. -/
theorem projectiveLinearNormalization_exists_native_sheaf_embedding
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
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
        Mono (nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE (m : ℤ) e hh 0) := by
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
  obtain ⟨m,hm,e,he,hhom⟩ :=
    projectiveLinearNormalization_exists_homogeneous_dual_embedding V L hL hinj hfinite
  have hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+(m : ℤ)) := by
    intro d ell hell
    exact nativeProjectiveRingIntegerPiece_mem_of_projection 𝓑 (d+(m : ℤ)) (e ell)
      (hhom d ell hell)
  exact ⟨m,hm,e,he,hh,
    nativeProjectiveModuleSheafMap_mono 𝓑 𝒟 ℰ hD hE (m : ℤ) e hh he 0⟩

end LinearStudy
