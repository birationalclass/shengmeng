module
public import Linear.NativeBaseSourceChartSections
public import Linear.ModuleBaseSourceOverlapRefinement
public import Linear.NativeGradedWeightedOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
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

/-- Actual base-localized weighted chart element yields an original
source sheaf section. Products retain their true denominator degree. -/
def nativeBaseSourceWeightedChartSection (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    nativeProjectiveModuleSections 𝓑 𝒟 hS 0 (op (Proj.basicOpen 𝓑 (algebraMap R S a))) :=
  nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hS d (algebraMap R S a)
    ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha)
    (nativeGradedBaseSourceChartEquiv 𝒜 𝓑 𝒟 hR hS d a ha
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) x)

theorem nativeBaseSourceWeightedChartSection_value (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a)
    (p : Proj.basicOpen 𝓑 (algebraMap R S a)) :
    (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) d a ha x).val p =
      nativeProjectiveChartRefinement 𝓑 (algebraMap R S a)
        (moduleBaseSourceLocalizationEquiv (S := S) a x.val) p := rfl

/-- The constructed base-to-source comparison commutes with ACTUAL
associated-module sheaf restriction, including the weighted overlap.
The proof passes to each original source prime; no naturality input is assumed. -/
theorem nativeBaseSourceWeightedChartSection_overlap
    (d e : ℕ) (a b : R) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 e)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    (nativeProjectiveModulePresheaf 𝓑 𝒟 hS 0).map
      (homOfLE (show Proj.basicOpen 𝓑 (algebraMap R S (a*b)) ≤
        Proj.basicOpen 𝓑 (algebraMap R S a) from by
          rw [map_mul]
          exact ProjectiveSpectrum.basicOpen_mul_le_left 𝓑 _ _)).op
      (nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) d a ha x) =
      nativeBaseSourceWeightedChartSection 𝒜 𝓑 𝒟 (hR := hR) (hS := hS) (d+e) (a*b)
        (SetLike.mul_mem_graded ha hb)
        (nativeGradedModuleWeightedOverlapMap 𝒜 𝒟 hR d e a b ha hb x) := by
  apply Subtype.ext
  funext p
  let T := p.1.asHomogeneousIdeal.toIdeal.primeCompl
  have hp : p.1 ∈ ProjectiveSpectrum.basicOpen 𝓑 ((algebraMap R S a)*(algebraMap R S b)) := by
    change (algebraMap R S a)*(algebraMap R S b) ∉ p.1.asHomogeneousIdeal
    have hp' := p.property
    change algebraMap R S (a*b) ∉ p.1.asHomogeneousIdeal at hp'
    simpa only [map_mul] using hp'
  have hpa : Submonoid.powers (algebraMap R S a) ≤ T :=
    Submonoid.powers_le.mpr (ProjectiveSpectrum.basicOpen_mul_le_left 𝓑 _ _ hp)
  have hpb : Submonoid.powers (algebraMap R S b) ≤ T :=
    Submonoid.powers_le.mpr (ProjectiveSpectrum.basicOpen_mul_le_right 𝓑 _ _ hp)
  with_unfolding_all exact
    (moduleBaseSourceLocalizationEquiv_overlap_refinement a b T hpa hpb x.val).symm
end LinearStudy
