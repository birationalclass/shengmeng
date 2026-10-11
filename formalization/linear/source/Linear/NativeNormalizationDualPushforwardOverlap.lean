module
public import Linear.NativeNormalizationPushforwardWeightedSections
public import Linear.NativeNormalizationWeightedChartRingActions
public import Linear.NativeBaseSourceWeightedSectionsLinear
public import Linear.NativeBaseSourceSectionsOverlap
public import Linear.NativeNormalizationPushforwardChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S D : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup D] [Module K D] [Module R D] [Module S D] [IsScalarTower R S D]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
variable (𝒟 : ℤ → Submodule K D)
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : D, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : D, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
  normalizationHomogeneousSourceChartAlgebra

/-- The SAME original dual/module section map respects actual global
pushforward restrictions on genuine weighted intersections. -/
theorem nativeNormalizationPushforwardWeightedChartSectionMap_original_overlap
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0
    let F := (Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M
    F.presheaf.map (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op
      (nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑 𝒟
        (hR := hR) (hS := hS) d a ha x) =
      nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑 𝒟
        (hR := hR) (hS := hS) (d+e) (a*b) (SetLike.mul_mem_graded ha hb)
        (nativeGradedModuleWeightedOverlapMap 𝒜 𝒟 hR d e a b ha hb x) := by
  dsimp only
  exact nativeBaseSourceWeightedChartSection_overlap 𝒜 𝓑 𝒟 (hR := hR) (hS := hS)
    d e a b ha hb x

end LinearStudy
