module
public import Linear.NativeBaseSourceSectionsOverlap
public import Linear.ProjectiveNativeBaseDualSections
public import Linear.ProjectiveNativeAffinePushforwardDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra
variable {n r : ℕ}

/-- The original finite linear projection's dual fraction sections commute
with the ACTUAL sheaf restriction to each source coordinate overlap.
All base/source grading compatibilities are derived from the original map. -/
theorem projectiveNormalization_native_base_dual_sections_overlap
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
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
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    letI : IsScalarTower A B D := IsScalarTower.of_compHom A B D
    ∀ ell : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 (MvPolynomial.X i),
      (nativeProjectiveModulePresheaf 𝓑 𝒟 hD 0).map
        (homOfLE (show Proj.basicOpen 𝓑 (φ (MvPolynomial.X i * MvPolynomial.X j)) ≤
          Proj.basicOpen 𝓑 (φ (MvPolynomial.X i)) from by
            rw [map_mul]
            exact ProjectiveSpectrum.basicOpen_mul_le_left 𝓑 _ _)).op
        (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟
          (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) (hS := hD)
          1 (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) ell) =
        nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟
          (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) (hS := hD)
          (1+1) (MvPolynomial.X i * MvPolynomial.X j)
          (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X ℂ i)
            (MvPolynomial.isHomogeneous_X ℂ j))
          (nativeGradedModuleWeightedOverlapMap 𝒜 𝒟
            (coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑)
            1 1 (MvPolynomial.X i) (MvPolynomial.X j)
            (MvPolynomial.isHomogeneous_X ℂ i) (MvPolynomial.isHomogeneous_X ℂ j) ell) := by
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
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  letI : IsScalarTower A B D := IsScalarTower.of_compHom A B D
  dsimp only
  intro ell
  exact nativeBaseSourceWeightedChartSection_overlap 𝒜 𝓑 𝒟
    (hR := coextensionNormalizationBaseGradeCompatibility 𝒜 𝓑) (hS := hD)
    1 1 (MvPolynomial.X i) (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X ℂ i) (MvPolynomial.isHomogeneous_X ℂ j) ell
end LinearStudy
