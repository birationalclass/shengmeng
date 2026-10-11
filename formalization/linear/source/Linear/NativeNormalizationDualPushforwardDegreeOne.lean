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

/-- The positive-degree source comparison at degree one is exactly the
original one-chart section map, on every original dual/module element. -/
theorem nativeNormalizationPushforwardWeightedChartSectionMap_degree_one_value
    (a : R) (ha : a ∈ 𝒜 1)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a) :
    nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑 𝒟
      (hR := hR) (hS := hS) 1 a ha x =
      nativeNormalizationPushforwardChartSectionMap 𝒜 𝓑 𝒟
        (hR := hR) (hS := hS) a ha
        ((LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝒜 𝒟 a)) x) := by
  apply Subtype.ext
  funext p
  rfl
end LinearStudy
