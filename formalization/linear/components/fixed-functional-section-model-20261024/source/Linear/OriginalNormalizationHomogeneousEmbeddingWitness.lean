module
public import Linear.ProjectiveNormalizationEmbeddingAboveBound
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
/-- Retain the full homogeneous embedding property of the SAME original
normalization map above any lower bound. This deliberately discards only
unused sheaf-local-free proof fields from the existing proved theorem. -/
theorem originalNormalizationDual_exists_homogeneous_embedding_witness_above
    {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (lower : ℕ) :
  let R := MvPolynomial (Fin (r+1)) ℂ
    let S := CoordinateRing n ⧸ V.ideal.toIdeal
    let phi := projectiveLinearNormalizationMap V L
    letI : Algebra R S := phi.toRingHom.toAlgebra
    letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun a => (phi.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let A := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let B := homogeneousQuotientPiece V.ideal.toIdeal
    letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
    let C := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
    ∃ m : ℕ,lower ≤ m ∧ 0 < m ∧ ∃ e : C →ₗ[S] S,Function.Injective e ∧
    ∀ d : ℤ,∀ z : C,z ∈ coextensionGradedPiece A B d →
      e z ∈ nativeProjectiveRingIntegerPiece B (d+(m:ℤ)) := by
  let R := MvPolynomial (Fin (r+1)) ℂ
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let phi := projectiveLinearNormalizationMap V L
  letI : Algebra R S := phi.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun a => (phi.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let A := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
  obtain ⟨m,hbound,hm,e,he,hh,hmono,hfree,hqc⟩ :=
    projectiveLinearNormalization_exists_native_embedding_above (n:=n) (r:=r) V L hL hinj hfinite lower
  exact ⟨m,hbound,hm,e,he,hh⟩
end LinearStudy
