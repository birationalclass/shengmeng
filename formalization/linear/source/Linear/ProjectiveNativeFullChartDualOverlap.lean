module
public import Linear.NativeFullChartDualOverlap
public import Linear.ProjectiveNativeFullSourceDualMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- On every ORIGINAL pair of normalization coordinates of V, the actual
full-source-chart dual comparison preserves its value under the ACTUAL
homogeneous overlap restriction. The actual restricted dual/source fractions
are constructed; no canonical or restriction certificate is supplied. -/
theorem projectiveNormalizationNativeFullSourceDualMap_overlap_value
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite)
    (i j : Fin (r+1)) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    letI : Module.Finite A B := hfinite
    letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    let a := (MvPolynomial.X i : A)
    let b := (MvPolynomial.X j : A)
    ∀ ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a,
    ∀ y : HomogeneousLocalization.Away 𝓑 (algebraMap A B a),
      finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away (a*b))
        (Submonoid.powers (a*b))
        (IsLocalization.injective (Localization.Away (a*b))
          (powers_le_nonZeroDivisors_of_noZeroDivisors
            (mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j))))
        (originalLocalizedModuleAwayOverlap a b ell.val)
        (originalLocalizedModuleAwayOverlap a b
          ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a
            (MvPolynomial.isHomogeneous_X ℂ i)).symm y).val) =
        (HomogeneousLocalization.awayMap 𝒜 (MvPolynomial.isHomogeneous_X ℂ j)
          (rfl : a*b=a*b)
          (projectiveNormalizationNativeFullSourceDualMap V L hL hfinite i ell y)).val := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : Module.Finite A B := hfinite
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  dsimp only
  intro ell y
  with_unfolding_all exact (finiteNativeDualFullSourceChartMap_overlap_value
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) (MvPolynomial.X i) (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X ℂ i) (MvPolynomial.isHomogeneous_X ℂ j)
    (IsLocalization.injective (Localization.Away (MvPolynomial.X i : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))
    (IsLocalization.injective (Localization.Away ((MvPolynomial.X i : A)*MvPolynomial.X j))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j)))) ell y)
end LinearStudy
