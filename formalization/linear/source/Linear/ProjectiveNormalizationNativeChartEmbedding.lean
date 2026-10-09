module
public import Linear.NativeGradedModuleAway
public import Linear.ProjectiveNormalizationHomogeneousEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
variable {n r : ℕ}

/-- The ORIGINAL finite normalization dual has actual injections on
every native degree-one Proj chart, with ONE positive twist m chosen
before the chart. The source and target use actual mathlib localizations.
Canonical-sheaf identification and global sheaf gluing are separate. -/
theorem projectiveLinearNormalization_exists_native_chart_embeddings
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
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    let 𝒟 := coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ) 𝓑
    ∃ m : ℕ, 0 < m ∧ ∃ e : D →ₗ[B] B, Function.Injective e ∧
      ∃ hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d →
        e ell = gradedIntegerProjection 𝓑 (d+(m : ℤ)) (e ell),
        ∀ a : B, ∀ ha : a ∈ 𝓑 1,
          Function.Injective (nativeGradedModuleAwayTwistEmbedding 𝓑 𝒟 a ha m e hh) := by
  letI := V.prime
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  let 𝒟 := coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ) 𝓑
  obtain ⟨m,hm,e,he,hh⟩ := projectiveLinearNormalization_exists_homogeneous_dual_embedding
    V L hL hinj hfinite
  exact ⟨m,hm,e,he,hh,fun a ha =>
    nativeGradedModuleAwayTwistEmbedding_injective 𝓑 𝒟 a ha m e he hh⟩

end LinearStudy
