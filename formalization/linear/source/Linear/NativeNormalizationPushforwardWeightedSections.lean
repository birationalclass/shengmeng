module
public import Linear.NativeNormalizationWeightedChartRingActions
public import Linear.NativeBaseSourceWeightedSectionsLinear
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

/-- The original fraction section map is LINEAR into sections of the
ACTUAL global normalization pushforward, with its actual base chart action.
The comparison is constructed, not supplied as a linearity certificate. -/
def nativeNormalizationPushforwardWeightedChartSectionMap (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) :
    let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0
    letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a →ₗ[HomogeneousLocalization.Away 𝒜 a]
      Γ((Scheme.Modules.pushforward (nativeNormalizationProjectiveMap 𝒜 𝓑)).obj M,
        Proj.basicOpen 𝒜 a) := by
  let M := nativeProjectiveModuleSheaf 𝓑 𝒟 hS 0
  letI := nativeNormalizationPushforwardChartModule 𝒜 𝓑 a M
  let theta := nativeBaseSourceWeightedChartSectionLinearMap 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) d a ha
  exact {
    toFun ell := theta ell
    map_add' ell k := theta.map_add ell k
    map_smul' c ell := by
      change theta (c • ell) = _
      refine (theta.map_smulₛₗ c ell).trans ?_
      exact (nativeNormalizationProjectiveMap_pushforward_weighted_chart_smul 𝒜 𝓑 d a ha M c
        (theta ell)).symm }

/-- The actual weighted pushforward map is bijective once its actual native
source section map is bijective. This hypothesis is derived on original V. -/
theorem nativeNormalizationPushforwardWeightedChartSectionMap_bijective
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (hs : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha))) :
    Function.Bijective (nativeNormalizationPushforwardWeightedChartSectionMap 𝒜 𝓑 𝒟
      (hR := hR) (hS := hS) d a ha) :=
  nativeBaseSourceWeightedChartSectionLinearMap_bijective 𝒜 𝓑 𝒟
    (hR := hR) (hS := hS) d a ha hs

end LinearStudy
