module
public import Linear.NormalizationSourceChartFinite
public import Linear.ProjectiveNormalizationSourceChartEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- Every FULL original normalization/source chart is a finite module
over the actual base chart, for the SAME finite normalization of V. -/
theorem projectiveNormalizationNativeSourceChart_finite
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
    Module.Finite
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
        (MvPolynomial.X i))
      (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
        (algebraMap A B (MvPolynomial.X i))) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : Module.Finite A B := hfinite
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  with_unfolding_all exact (normalizationHomogeneousChart_finite
    (K := ℂ) (R := A) (S := B)
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i))

/-- Construct the normalization from original V, with finite actual FULL
source chart modules at every original coordinate. No abstract finite
chart model or finite-free/CM input is added. -/
theorem projective_exists_normalization_native_finite_source_charts
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
      ∃ hL : ∀ i, (L i).IsHomogeneous 1,
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∀ i : Fin (r+1),
          let A := MvPolynomial (Fin (r+1)) ℂ
          let B := CoordinateRing n ⧸ V.ideal.toIdeal
          let φ := projectiveLinearNormalizationMap V L
          letI : Algebra A B := φ.toRingHom.toAlgebra
          letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
          letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
          letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
            (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
          Module.Finite
            (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
              (MvPolynomial.X i))
            (HomogeneousLocalization.Away (homogeneousQuotientPiece V.ideal.toIdeal)
              (algebraMap A B (MvPolynomial.X i))) := by
  obtain ⟨r,hr,hdim,L,hL,hinj,hfinite,_⟩ :=
    projective_exists_normalization_native_source_charts V x hx
  refine ⟨r,hr,hdim,L,hL,hinj,hfinite,?_⟩
  intro i
  exact projectiveNormalizationNativeSourceChart_finite V L hL hfinite i

end LinearStudy
