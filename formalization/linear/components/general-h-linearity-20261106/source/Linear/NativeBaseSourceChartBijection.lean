module
public import Linear.NativeProjectiveChartInjectiveAll
public import Linear.NativeFiniteGradedChartSectionsSurjective
public import Linear.NativeBaseSourceSectionsOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [IsScalarTower K S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsDomain S] [Module.IsTorsionFree S M]

/-- The actual base-localized to source-section map separates weighted
fractions on every positive-degree source chart. No torsion-freeness over
the base ring is assumed; quotient modules therefore satisfy the hypotheses. -/
theorem nativeBaseSourceWeightedChartSection_injective
    (d : ℕ) (hd : 0 < d) (a : R) (ha : a ∈ 𝒜 d) :
    Function.Injective
      (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS d a ha) := by
  exact (nativeProjectiveChartDegreeZeroSectionMap_injective_all 𝓑 𝒟 hS
    d hd (algebraMap R S a) ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)).comp
      (nativeGradedBaseSourceChartEquiv 𝒜 𝓑 𝒟 hR hS d a ha
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)).injective

/-- Degree-one chart surjectivity is derived from the finite graded source
module. The comparison uses the actual scalar map and actual localized
fractions, including empty charts. No chart bijection is supplied. -/
theorem nativeBaseSourceWeightedChartSection_bijective
    [DirectSum.Decomposition 𝒟] [IsNoetherianRing S] [Module.Finite S M]
    {ι : Type u} (coords : ι → S) (hcoords : ∀ i, coords i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range coords) = ⊤)
    (a : R) (ha : a ∈ 𝒜 1) :
    Function.Bijective
      (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 hR hS 1 a ha) := by
  exact ⟨nativeBaseSourceWeightedChartSection_injective 𝒜 𝓑 𝒟 hR hS 1 (by decide) a ha,
    (nativeFiniteGradedChartDegreeZeroSectionMap_surjective 𝓑 𝒟 hS
      coords hcoords hgen (algebraMap R S a)
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)).comp
      (nativeGradedBaseSourceChartEquiv 𝒜 𝓑 𝒟 hR hS 1 a ha
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)).surjective⟩
end LinearStudy
