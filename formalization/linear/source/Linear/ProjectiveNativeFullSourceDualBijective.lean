module
public import Linear.NativeDualFullSourceChartEquiv
public import Linear.ProjectiveNativeFullSourceDualMap
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

/-- The comparison at each ORIGINAL normalization coordinate is bijective.
This compares the actual native dual chart and FULL actual source chart;
it does not supply the canonical-sheaf identification. -/
theorem projectiveNormalizationNativeFullSourceDualMap_bijective
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
    Function.Bijective (projectiveNormalizationNativeFullSourceDualMap V L hL hfinite i) := by
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
  with_unfolding_all exact (finiteNativeDualFullSourceChartMap_bijective
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i)
    (IsLocalization.injective (Localization.Away (MvPolynomial.X i : A))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i))))

end LinearStudy
