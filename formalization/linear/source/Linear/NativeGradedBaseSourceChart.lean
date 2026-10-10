module
public import Linear.ModuleBaseSourceLocalization
public import Linear.NativeGradedChartSingleFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M]
variable [IsScalarTower R S M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- The universal localization comparison preserves the ACTUAL homogeneous
degree-zero charts in both directions, for the same original module grading.
Both sides use their own original ring actions; the proof uses exact fractions. -/
theorem nativeGradedBaseSourceChart_mem_iff
    (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (haS : algebraMap R S a ∈ 𝓑 d)
    (x : LocalizedModule (Submonoid.powers a) M) :
    moduleBaseSourceLocalizationEquiv (S := S) a x ∈
      nativeGradedModuleAwayDegreeZero 𝓑 𝒟 d (algebraMap R S a) ↔
      x ∈ nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a := by
  constructor
  · intro hx
    obtain ⟨n,m,hm,he⟩ := nativeGradedChart_exists_singleFraction 𝓑 𝒟 hS d
      (algebraMap R S a) haS _ hx
    have heq : moduleBaseSourceLocalizationEquiv (S := S) a
        (LocalizedModule.mk m (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a)) =
        LocalizedModule.mk m
          (⟨(algebraMap R S a)^n,⟨n,rfl⟩⟩ : Submonoid.powers (algebraMap R S a)) := by
      rw [moduleBaseSourceLocalizationEquiv_mk]
      congr 1
      apply Subtype.ext
      exact map_pow (algebraMap R S) a n
    have hxval := (moduleBaseSourceLocalizationEquiv (S := S) a).injective (he.trans heq.symm)
    rw [hxval]
    exact Submodule.subset_span ⟨n,m,hm,rfl⟩
  · intro hx
    obtain ⟨n,m,hm,rfl⟩ := nativeGradedChart_exists_singleFraction 𝒜 𝒟 hR d a ha _ hx
    rw [moduleBaseSourceLocalizationEquiv_mk]
    apply Submodule.subset_span
    refine ⟨n,m,hm,?_⟩
    congr 1
    apply Subtype.ext
    exact map_pow (algebraMap R S) a n

/-- Restriction of the same exact universal comparison to homogeneous charts.
This construction does not assume a chart identification as an input. -/
def nativeGradedBaseSourceChartEquiv
    (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (haS : algebraMap R S a ∈ 𝓑 d) :
    nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a ≃
      nativeGradedModuleAwayDegreeZero 𝓑 𝒟 d (algebraMap R S a) :=
  Equiv.subtypeEquiv (moduleBaseSourceLocalizationEquiv (S := S) a).toEquiv
    (fun x => (nativeGradedBaseSourceChart_mem_iff 𝒜 𝓑 𝒟 hR hS d a ha haS x).symm)

theorem nativeGradedBaseSourceChartEquiv_apply
    (hR : ∀ n : ℕ, ∀ j : ℤ, ∀ b : R, b ∈ 𝒜 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (hS : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
      ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (haS : algebraMap R S a ∈ 𝓑 d)
    (x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 d a) :
    (nativeGradedBaseSourceChartEquiv 𝒜 𝓑 𝒟 hR hS d a ha haS x).val =
      moduleBaseSourceLocalizationEquiv (S := S) a x.val := rfl
end LinearStudy
