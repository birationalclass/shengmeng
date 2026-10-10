module
public import Linear.NativeGradedWeightedSingleFraction
public import Linear.NativeProjectiveChartSectionsInjective
public import Mathlib.Algebra.Module.LocalizedModule.Away
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
/-- The genuine module restriction is injective for a torsion-free module
on an integral ring with nonzero product coordinate. -/
theorem originalLocalizedModuleAwayOverlap_injective
    [IsDomain R] [Module.IsTorsionFree R M] (a b : R) (hab : a*b ≠ 0) :
    Function.Injective (originalLocalizedModuleAwayOverlap (M := M) a b) := by
  apply IsLocalizedModule.injective_of_map_zero (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
  intro m hm
  change originalLocalizedModuleAwayOverlap a b (LocalizedModule.mk m 1) = 0 at hm
  rw [originalLocalizedModuleAwayOverlap_mk_one] at hm
  have hz : LocalizedModule.mkLinearMap (Submonoid.powers (a*b)) M m = 0 := hm
  obtain ⟨t,ht⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (a*b))
    (LocalizedModule.mkLinearMap (Submonoid.powers (a*b)) M)).mp hz
  obtain ⟨n,hn⟩ := t.property
  have ht0 : (t : R) ≠ 0 := by rw [← hn]; exact pow_ne_zero n hab
  have hm0 : m = 0 := (smul_eq_zero_iff_right ht0).mp ht
  simp [hm0]
/-- Clear the ORIGINAL ratio b/a on the ACTUAL weighted degree-two module.
Every overlap element is obtained from the original degree-one chart after
multiplying by a power of the actual ratio. No abstract surjectivity field. -/
theorem nativeGradedModuleDegreeOneOverlap_surj
    (hgrade : ∀ n : ℕ, ∀ j : ℤ, ∀ c : R, c ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → c • m ∈ 𝒟 ((n : ℤ)+j))
    (a b : R) (ha : a ∈ 𝒜 1) (hb : b ∈ 𝒜 1)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 2 (a*b)) :
    ∃ n : ℕ, ∃ y : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a,
      (HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
        (HomogeneousLocalization.Away.isLocalizationElem ha hb))^n • x =
        nativeGradedModuleWeightedOverlapMap 𝒜 𝒟 hgrade 1 1 a b ha hb y := by
  obtain ⟨n,m,hm,hx⟩ := nativeGradedModuleAwayDegreeZero_exists_fraction
    𝒜 𝒟 hgrade 2 (a*b) (by simpa using SetLike.mul_mem_graded ha hb) x.val x.property
  let y : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a :=
    ⟨LocalizedModule.mk m (⟨a^(n*2),⟨n*2,rfl⟩⟩ : Submonoid.powers a),
      Submodule.subset_span ⟨n*2,m,by simpa only [mul_one] using hm,rfl⟩⟩
  refine ⟨n,y,?_⟩
  apply Subtype.ext
  change ((HomogeneousLocalization.awayMap 𝒜 hb (rfl : a*b=a*b)
    (HomogeneousLocalization.Away.isLocalizationElem ha hb))^n).val • x.val =
    originalLocalizedModuleAwayOverlap a b y.val
  rw [hx]
  dsimp only [y]
  rw [originalLocalizedModuleAwayOverlap_mk]
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.awayMap_mk,HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow,LocalizedModule.mk_smul_mk]
  congr 1
  · congr 1
    simp only [pow_one,mul_pow,← pow_add,mul_two]
  · apply Subtype.ext
    simp only [Submonoid.coe_mul,SubmonoidClass.coe_pow]
    simp only [pow_one,← pow_add,mul_two]
end LinearStudy
