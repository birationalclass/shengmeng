module
public import Linear.HomogeneousLocalizationIntegralValue
public import Linear.FiniteFunctionalLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- Every actual full-source-chart functional has a CONSTRUCTED original
integral homogeneous functional after clearing one original denominator.
Finiteness, not finite freeness or global Cohen--Macaulayness, is used. -/
theorem normalizationChartFunctional_exists_homogeneous_denominator
    (a : R) (ha : a ∈ 𝒜 1) (haB : algebraMap R S a ∈ 𝓑 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a)))
    (f : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)
      →ₗ[HomogeneousLocalization.Away 𝒜 a] HomogeneousLocalization.Away 𝒜 a) :
    ∃ m : ℕ, ∃ ψ : S →ₗ[R] R, ∀ n : ℕ, ∀ b : S, ∀ hb : b ∈ 𝓑 n,
      ψ b ∈ 𝒜 (n+m) ∧
      algebraMap R (Localization.Away a) (ψ b) =
        (algebraMap R (Localization.Away a) a)^(n+m) *
          (f (HomogeneousLocalization.Away.mk 𝓑 haB n b
            (by simpa using hb))).val := by
  obtain ⟨s,ψ,hψ⟩ := finiteLinearFunctional_exists_denominator
    (Submonoid.powers a) hinj (normalizationChartFunctionalLinearMap 𝒜 𝓑 a ha haB f)
  obtain ⟨m,hm⟩ := s.property
  refine ⟨m,ψ,?_⟩
  intro n b hb
  have heq : algebraMap R (Localization.Away a) (ψ b) =
      (algebraMap R (Localization.Away a) a)^(n+m) *
        (f (HomogeneousLocalization.Away.mk 𝓑 haB n b (by simpa using hb))).val := by
    have hval := LinearMap.congr_fun hψ b
    change algebraMap R (Localization.Away a) (ψ b) =
      (s : R) • normalizationChartFunctionalAddMap 𝒜 𝓑 a haB f b at hval
    rw [Algebra.smul_def,← hm,map_pow,
      normalizationChartFunctionalAddMap_homogeneous 𝒜 𝓑 a haB f n b hb] at hval
    exact hval.trans (by rw [pow_add]; ring)
  exact ⟨homogeneousLocalization_integral_value_mem 𝒜 a ha hinj
    (n+m) (ψ b) (f (HomogeneousLocalization.Away.mk 𝓑 haB n b
      (by simpa using hb))) heq,heq⟩
end LinearStudy
