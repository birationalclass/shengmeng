module
public import Linear.ProjectiveNormalizationGradedDual
public import Linear.CoextensionGradedEmbedding
public import Linear.HomogeneousPositiveEmbeddingShift
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
open CategoryTheory
variable {n r : ℕ}

/-- Construct a positive-degree homogeneous embedding of the ACTUAL
native dual of the original finite linear normalization. This does not
yet identify its projective associated sheaf with the canonical sheaf. -/
theorem projectiveLinearNormalization_exists_homogeneous_dual_embedding
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
    ∃ m : ℕ, 0 < m ∧
      ∃ e : (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A) →ₗ[B] B,
        Function.Injective e ∧ ∀ d : ℤ, ∀ ell,
          ell ∈ coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
            (homogeneousQuotientPiece V.ideal.toIdeal) d →
          e ell = gradedIntegerProjection (homogeneousQuotientPiece V.ideal.toIdeal)
            (d+(m : ℤ)) (e ell) := by
  letI := V.prime
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : Module.Finite A B := hfinite
  letI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  obtain ⟨k,e,he,hhom⟩ := coextensionDual_exists_homogeneous_embedding
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ) (homogeneousQuotientPiece V.ideal.toIdeal)
  have hb : φ (MvPolynomial.X (0 : Fin (r+1))) ∈ homogeneousQuotientPiece V.ideal.toIdeal 1 := by
    apply (homogeneousQuotientPiece_mem_iff _ _ _).mpr
    refine ⟨L 0,hL 0,?_⟩
    simp only [φ,projectiveLinearNormalizationMap,AlgHom.comp_apply,MvPolynomial.aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
  have hne : φ (MvPolynomial.X (0 : Fin (r+1))) ≠ 0 := by
    intro hz
    apply MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (r+1))
    apply hinj
    simpa only [map_zero] using hz
  exact homogeneous_embedding_exists_positive_shift (homogeneousQuotientPiece V.ideal.toIdeal)
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal)) k e he hhom
    (φ (MvPolynomial.X (0 : Fin (r+1)))) hb hne

/-- Construct both the original finite linear normalization and a
positive-degree homogeneous injection of its ACTUAL native dual.
Neither a graded dual, an embedding nor a degree shift is an input. -/
theorem projective_exists_linear_normalization_with_homogeneous_dual_embedding
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
        (∀ i, (L i).IsHomogeneous 1) ∧
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        let A := MvPolynomial (Fin (r+1)) ℂ
        let B := CoordinateRing n ⧸ V.ideal.toIdeal
        let φ := projectiveLinearNormalizationMap V L
        letI : Algebra A B := φ.toRingHom.toAlgebra
        letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
        letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
        ∃ m : ℕ, 0 < m ∧
          ∃ e : (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A) →ₗ[B] B,
            Function.Injective e ∧ ∀ d : ℤ, ∀ ell,
              ell ∈ coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
                (homogeneousQuotientPiece V.ideal.toIdeal) d →
              e ell = gradedIntegerProjection (homogeneousQuotientPiece V.ideal.toIdeal)
                (d+(m : ℤ)) (e ell) := by
  obtain ⟨r,hr,hdim,L,hL,hinj,hfinite,_⟩ :=
    projective_exists_linear_normalization_chart_dimension V x hx
  exact ⟨r,hr,hdim,L,hL,hinj,hfinite,
    projectiveLinearNormalization_exists_homogeneous_dual_embedding V L hL hinj hfinite⟩

end LinearStudy
