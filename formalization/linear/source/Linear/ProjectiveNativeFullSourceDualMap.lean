module
public import Linear.NativeDualFullSourceChartComparison
public import Linear.ProjectiveNormalizationSourceChartEquiv
public import Linear.ProjectiveNormalizationGradedDual
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000
namespace LinearStudy
open CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- At each ORIGINAL normalization coordinate, construct the actual
degree-zero dual comparison MAP. Its target is the actual linear dual
of the FULL actual original homogeneous source chart. Surjectivity
and the canonical-sheaf identification remain separate. -/
def projectiveNormalizationNativeFullSourceDualMap
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
    let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
    let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
    let a := (MvPolynomial.X i : A)
    nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a
      →ₗ[HomogeneousLocalization.Away 𝒜 a]
        (HomogeneousLocalization.Away 𝓑 (algebraMap A B a)
          →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) := by
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
  exact finiteNativeDualFullSourceChartMap
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i)
    (IsLocalization.injective (Localization.Away (MvPolynomial.X i : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))

/-- The ORIGINAL degree-zero comparison retains the original native
dual/source localization evaluation. -/
theorem projectiveNormalizationNativeFullSourceDualMap_apply
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
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
    ∀ ell : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a,
    ∀ x : HomogeneousLocalization.Away 𝓑 (algebraMap A B a),
      (projectiveNormalizationNativeFullSourceDualMap V L hL hfinite i ell x).val =
        finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
          (Submonoid.powers a)
          (IsLocalization.injective (Localization.Away a)
            (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))
          ell.val ((nativeNormalizationSourceChartEquiv 𝒜 𝓑 a
            (MvPolynomial.isHomogeneous_X ℂ i)).symm x).val := by
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
  intro ell x
  with_unfolding_all exact (finiteNativeDualFullSourceChartMap_apply_val
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i)
    (IsLocalization.injective (Localization.Away (MvPolynomial.X i : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))) ell x)

end LinearStudy
