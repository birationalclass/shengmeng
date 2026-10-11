module
public import Linear.NativeNormalizationPushforwardGlobalHomWeightedLinear
public import Linear.ProjectiveNativeWeightedSourceSectionsBijective
public import Linear.NormalizationHomogeneousOverlapInjective
public import Linear.ProjectiveNativeDualChartSectionsBijective
public import Linear.NativeAffineInternalHomLinear
public import Linear.NativeCoextensionBaseSourceCharts
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

/-- For the SAME ORIGINAL V and finite injective linear normalization,
actual sections of the global finite-dual pushforward are linearly equivalent
to ACTUAL global internal Hom chart sections. Source-section bijectivity is
derived from the original normalization, not given as a chart certificate. -/
def projectiveNormalization_native_global_weighted_overlap_duality_linearEquiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i j : Fin (r+1)) :=
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
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  letI : IsScalarTower A B D := IsScalarTower.of_compHom A B D
  let 𝒟 := coextensionGradedPiece 𝒜 𝓑
  let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let a : A := MvPolynomial.X i
  let b : A := MvPolynomial.X j
  let ha : a ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ i
  let hb : b ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X ℂ j
  have hs : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2
      (algebraMap A B (a*b)) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem
        (SetLike.mul_mem_graded ha hb))) := by
    have transport {c z : B} (hc : c ∈ 𝓑 2) (hz : z ∈ 𝓑 2) (h : c = z)
        (H : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2 c hc)) :
        Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2 z hz) := by
      subst z
      exact H
    exact transport _ _ (φ.map_mul (MvPolynomial.X i) (MvPolynomial.X j)).symm
      (projectiveNormalization_native_dual_weighted_overlap_sections_bijective V L hL hinj hfinite i j)
  nativeNormalizationPushforwardGlobalHomWeightedOverlapLinearEquiv (K := ℂ) (R := A) (S := B) 𝒜 𝓑 a b ha hb
    (mul_ne_zero (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j))
    (IsLocalization.injective (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero i)))
    (projectiveCoordinateHomogeneousOverlap_injective r i j) hs

end LinearStudy
