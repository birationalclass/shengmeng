module
public import Linear.NativeBaseSourceSectionsOverlap
public import Linear.NativeProjectiveChartSectionsOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- The actual weighted overlap map with an explicitly named product.
This permits both a,b and b,a restrictions to share the SAME original chart. -/
def nativeGradedModuleWeightedOverlapTo
    (d e : ℕ) (a b c : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) (hc : c = a*b)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 (d+e) c := by
  subst c
  exact nativeGradedModuleWeightedOverlapMap 𝒜 𝒟 hR d e a b ha hb x

/-- Naming the target product changes no actual base restriction. -/
theorem nativeProjectiveChartDegreeZeroSectionMap_overlap_to
    (d e : ℕ) (a b c : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) (hc : c = a*b)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    (nativeProjectiveModulePresheaf 𝒜 𝒟 hR 0).map
      (homOfLE (show Proj.basicOpen 𝒜 c ≤ Proj.basicOpen 𝒜 a from by
        rw [hc]; exact ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op
      (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR d a ha x) =
    nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hR (d+e) c
      (by rw [hc]; exact SetLike.mul_mem_graded ha hb)
      (nativeGradedModuleWeightedOverlapTo 𝒜 𝒟 hR d e a b c ha hb hc x) := by
  subst c
  exact nativeProjectiveChartDegreeZeroSectionMap_overlap 𝒜 𝒟 hR d e a b ha hb x

/-- The SAME named product also retains the actual source restriction. -/
theorem nativeBaseSourceWeightedChartSection_overlap_to
    (d e : ℕ) (a b c : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e) (hc : c = a*b)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map
      (homOfLE (show Proj.basicOpen 𝓑 (algebraMap R S c) ≤
        Proj.basicOpen 𝓑 (algebraMap R S a) from by
          rw [hc,map_mul]; exact ProjectiveSpectrum.basicOpen_mul_le_left 𝓑 _ _)).op
      (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS d a ha x) =
    nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS (d+e) c
      (by rw [hc]; exact SetLike.mul_mem_graded ha hb)
      (nativeGradedModuleWeightedOverlapTo 𝒜 𝒟 hR d e a b c ha hb hc x) := by
  subst c
  exact nativeBaseSourceWeightedChartSection_overlap 𝒜 𝓑 𝒟 hR hS d e a b ha hb x
end LinearStudy
