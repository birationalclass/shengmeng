module
public import Linear.NativeGradedWeightedBaseSourceMap
public import Linear.NativeBaseSourceSectionsOverlap
public import Linear.NativeProjectiveChartSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- SAME original weighted source section map, with the actual normalization
chart scalar action. Arbitrary-degree homogeneous fractions retain their degree. -/
def nativeBaseSourceWeightedChartSectionLinearMap (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) :
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a
      →ₛₗ[((Proj.awayToSection 𝓑 (algebraMap R S a)).hom).comp
        (normalizationHomogeneousChartMap 𝒜 𝓑 a)]
      nativeProjectiveModuleSections 𝓑 𝒟 hS 0
        (op (Proj.basicOpen 𝓑 (algebraMap R S a))) := by
  let f := normalizationHomogeneousChartMap 𝒜 𝓑 a
  let g := (ProjectiveSpectrum.Proj.awayToSection 𝓑 (algebraMap R S a)).hom
  letI : RingHomCompTriple f g (g.comp f) := ⟨rfl⟩
  exact (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS d (algebraMap R S a)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)).comp
      (nativeGradedWeightedBaseSourceChartMap 𝒜 𝓑 𝒟 hR hS d a ha)

/-- This semilinear map is exactly the already specified weighted source
section map, not only an unspecified equivalence between its two objects. -/
theorem nativeBaseSourceWeightedChartSectionLinearMap_eq (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    nativeBaseSourceWeightedChartSectionLinearMap 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) d a ha x =
      nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) d a ha x := rfl

/-- Actual weighted section bijectivity follows from the source chart theorem
and the SAME universal localization map on the original module. -/
theorem nativeBaseSourceWeightedChartSectionLinearMap_bijective
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (hs : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha))) :
    Function.Bijective (nativeBaseSourceWeightedChartSectionLinearMap 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) d a ha) :=
  hs.comp (nativeGradedWeightedBaseSourceChartMap_bijective 𝒜 𝓑 𝒟 hR hS d a ha)

end LinearStudy
