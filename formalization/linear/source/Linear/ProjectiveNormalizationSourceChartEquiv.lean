module
public import Linear.NormalizationSourceChartEquiv
public import Linear.ProjectiveNativeDegreeZeroDualMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- At each ORIGINAL normalization coordinate, identify the original generated
source chart with the FULL homogeneous Proj chart of the same original V. -/
def projectiveNormalizationNativeSourceChartEquiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1) (i : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    let a := (MvPolynomial.X i : A)
    nativeNormalizationSourceAwayZero 𝒜 𝓑 a ≃ₗ[HomogeneousLocalization.Away 𝒜 a]
      HomogeneousLocalization.Away 𝓑 (algebraMap A B a) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  with_unfolding_all exact (nativeNormalizationSourceChartEquiv
    (K := ℂ) (R := A) (S := B)
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i))

/-- The same normalization constructed from original V has complete source-chart
equivalences at EVERY coordinate; neither an abstract chart nor an extra
finite-free/CM condition is supplied. -/
theorem projective_exists_normalization_native_source_charts
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    ∃ r : ℕ, r ≤ n ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal) = (r : WithBot ℕ∞) ∧
      ∃ L : Fin (r+1) → CoordinateRing n,
      ∃ hL : ∀ i, (L i).IsHomogeneous 1,
        Function.Injective (projectiveLinearNormalizationMap V L) ∧
        (projectiveLinearNormalizationMap V L).Finite ∧
        ∀ i, Function.Bijective (projectiveNormalizationNativeSourceChartEquiv V L hL i) := by
  obtain ⟨r,hr,hdim,L,hL,hinj,hfinite,_⟩ :=
    projective_exists_linear_normalization_chart_dimension V x hx
  refine ⟨r,hr,hdim,L,hL,hinj,hfinite,?_⟩
  intro i
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  exact (projectiveNormalizationNativeSourceChartEquiv V L hL i).bijective

end LinearStudy
