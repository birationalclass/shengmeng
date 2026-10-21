module
public import Linear.NativeProjectiveChartSections
public import Linear.NativeGradedWeightedOverlap
public import Linear.LocalizedModuleAwayOverlapRefinement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
variable (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ a : R, a ∈ 𝒜 n →
  ∀ m : M, m ∈ 𝒟 j → a • m ∈ 𝒟 ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar
  nativeProjectiveAmbientSectionModule

/-- Chart-to-section comparison commutes with the ACTUAL associated
module presheaf restriction on the original Proj. The overlap has the
correct denominator degree d+e, and no compatibility model is assumed. -/
theorem nativeProjectiveChartDegreeZeroSectionMap_overlap
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    (nativeProjectiveModulePresheaf 𝒜 𝒟 hgrade 0).map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b)).op
      (nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hgrade d a ha x) =
    nativeProjectiveChartDegreeZeroSectionMap 𝒜 𝒟 hgrade (d+e) (a*b)
      (SetLike.mul_mem_graded ha hb)
      (nativeGradedModuleWeightedOverlapMap 𝒜 𝒟 hgrade d e a b ha hb x) := by
  apply Subtype.ext
  funext p
  let T := p.1.asHomogeneousIdeal.toIdeal.primeCompl
  have hpa : Submonoid.powers a ≤ T :=
    Submonoid.powers_le.mpr (ProjectiveSpectrum.basicOpen_mul_le_left 𝒜 a b p.property)
  have hpb : Submonoid.powers b ≤ T :=
    Submonoid.powers_le.mpr (ProjectiveSpectrum.basicOpen_mul_le_right 𝒜 a b p.property)
  with_unfolding_all exact
    (originalLocalizedModuleAwayOverlap_refinement a b T hpa hpb x.val).symm
end LinearStudy
