module
public import Linear.NativeDualGlobalHomOriginalWeightedOverlapRestriction
public import Linear.ProjectiveNativeGlobalWeightedOverlapDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option diagnostics true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
attribute [local irreducible] nativeNormalizationProjectiveMap
  nativeDualGlobalHomChartLinearEquiv nativeDualGlobalHomWeightedOverlapLinearEquiv
  schemeModuleHomModuleSheaf
variable {n r : ℕ}

/-- Every original coordinate pair has entire native-dual/global-Hom
restriction equality. Coordinate nonvanishing and localization injectivity
are derived; no desired restriction equation is supplied. -/
theorem projectiveNormalization_native_original_dual_hom_overlap_restriction
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i j : Fin (r+1)) :
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  letI : Module.Finite A B := hfinite
  let a : A := MvPolynomial.X i
  let b : A := MvPolynomial.X j
  let ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  let hb : b ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ j
  let hab : a*b ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j)
  let hinja : Function.Injective (algebraMap A (Localization.Away a)) :=
    IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (show a ≠ 0 from MvPolynomial.X_ne_zero i))
  let hinj := projectiveCoordinateHomogeneousOverlap_injective r i j
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  ∀ ell : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a,
  let P := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj
    (SheafOfModules.unit (Proj 𝓑).ringCatSheaf)
  let Q : (Proj 𝒜).Modules := SheafOfModules.unit (Proj 𝒜).ringCatSheaf
  let H := schemeModuleHomModuleSheaf P Q
  let inc := homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)
  let ell0 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)) ell
  H.presheaf.map inc.op (nativeDualGlobalHomChartLinearEquiv 𝒜 𝓑 a ha hinja ell0) =
    (nativeDualGlobalHomWeightedOverlapLinearEquiv 𝒜 𝓑 a b ha hb hab hinja hinj).toEquiv
      (nativeGradedModuleWeightedOverlapMap 𝒜 𝒟
        (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) 1 1 a b ha hb ell) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  letI : Module.Finite A B := hfinite
  let a : A := MvPolynomial.X i
  let b : A := MvPolynomial.X j
  let ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  let hb : b ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ j
  let hab : a*b ≠ 0 := mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j)
  let hinja : Function.Injective (algebraMap A (Localization.Away a)) :=
    IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (show a ≠ 0 from MvPolynomial.X_ne_zero i))
  let hinj := projectiveCoordinateHomogeneousOverlap_injective r i j
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  dsimp only
  intro ell
  exact nativeDualGlobalHom_original_weighted_overlap_restriction 𝒜 𝓑 a b ha hb hab hinja hinj ell
end LinearStudy
