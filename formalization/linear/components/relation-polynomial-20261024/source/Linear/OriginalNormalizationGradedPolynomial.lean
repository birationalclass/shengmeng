module
public import Linear.ProjectiveNormalizationEmbeddingAboveBound
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
/-- Choose ONE original graded embedding degree m ABOVE a fixed lower
bound BEFORE ALL nonzero degree-zero dual elements. Its actual image is
lifted to an ORIGINAL degree-m polynomial Q with Q not in V's ideal.
No canonical identification or prescribed cut support is claimed. -/
theorem originalNormalizationDual_exists_fixed_polynomial_images_above
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
      ∀ z : C,z ∈ coextensionGradedPiece A B 0 → z ≠ 0 →
        ∃ Q : CoordinateRing n,Q.IsHomogeneous m ∧ Q ∉ V.ideal.toIdeal ∧
          Ideal.Quotient.mk V.ideal.toIdeal Q=e z := by
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
    projectiveLinearNormalization_exists_native_embedding_above V L hL hinj hfinite lower
  refine ⟨m,hbound,hm,e,he,?_⟩
  intro z hz hne
  have himage : e z ∈ B m := by
    simpa only [zero_add,nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,if_true,
      Int.toNat_natCast] using hh 0 z hz
  obtain ⟨Q,hQ,hval⟩ := (homogeneousQuotientPiece_mem_iff V.ideal.toIdeal m (e z)).mp himage
  refine ⟨Q,hQ,?_,hval⟩
  intro hmem
  apply hne
  apply he
  rw [map_zero,← hval]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
end LinearStudy
