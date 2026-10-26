module
public import Linear.NativeGradedBaseSourceScalar
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [SetLike.GradedSMul 𝒜 𝓑]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- Exact semilinear comparison of the actual charts of the SAME module.
The scalar hom is the original normalization's homogeneous chart map. -/
def nativeGradedBaseSourceChartMap
    (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (a : R) (ha : a ∈ 𝒜 1) :
    nativeGradedModuleAwayZero 𝒜 𝒟 a →ₛₗ[normalizationHomogeneousChartMap 𝒜 𝓑 a]
      nativeGradedModuleAwayZero 𝓑 𝒟 (algebraMap R S a) where
  toFun x := ⟨moduleBaseSourceLocalizationEquiv (S := S) a x.val,by
    have hx : x.val ∈ nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 a := by
      simpa only [nativeGradedModuleAwayDegreeZero_one] using x.property
    have h := (nativeGradedBaseSourceChart_mem_iff 𝒜 𝓑 𝒟 hR hS 1 a ha
      ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) x.val).mpr hx
    rwa [nativeGradedModuleAwayDegreeZero_one] at h⟩
  map_add' x y := Subtype.ext ((moduleBaseSourceLocalizationEquiv (S := S) a).map_add x.val y.val)
  map_smul' c x := Subtype.ext (moduleBaseSourceLocalizationEquiv_chart_smul 𝒜 𝓑 a ha c x.val)

theorem nativeGradedBaseSourceChartMap_bijective
    (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (a : R) (ha : a ∈ 𝒜 1) :
    Function.Bijective (nativeGradedBaseSourceChartMap 𝒜 𝓑 𝒟 hR hS a ha) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact (moduleBaseSourceLocalizationEquiv (S := S) a).injective (congrArg Subtype.val hxy)
  · intro y
    let x := (moduleBaseSourceLocalizationEquiv (S := S) a).symm y.val
    have hx : x ∈ nativeGradedModuleAwayZero 𝒜 𝒟 a := by
      have hy : y.val ∈ nativeGradedModuleAwayDegreeZero 𝓑 𝒟 1 (algebraMap R S a) := by
        simpa only [nativeGradedModuleAwayDegreeZero_one] using y.property
      have h := (nativeGradedBaseSourceChart_mem_iff 𝒜 𝓑 𝒟 hR hS 1 a ha
        ((normalizationBaseGradedRingHom 𝒜 𝓑).map_mem ha) x).mp (by simpa [x] using hy)
      rwa [nativeGradedModuleAwayDegreeZero_one] at h
    exact ⟨⟨x,hx⟩,Subtype.ext ((moduleBaseSourceLocalizationEquiv (S := S) a).apply_symm_apply y.val)⟩

theorem nativeGradedBaseSourceChartMap_mk
    (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (a : R) (ha : a ∈ 𝒜 1) (n : ℕ) (m : M) (hm : m ∈ 𝒟 (n : ℤ)) :
    (nativeGradedBaseSourceChartMap 𝒜 𝓑 𝒟 hR hS a ha
      ⟨LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a),
        Submodule.subset_span ⟨n,m,hm,rfl⟩⟩).val =
      LocalizedModule.mk m (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a)) := by
  change moduleBaseSourceLocalizationEquiv (S := S) a _ = _
  rw [moduleBaseSourceLocalizationEquiv_mk]
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap R S) a n
end LinearStudy
