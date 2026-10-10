module
public import Linear.NormalizationSourceChartLinearMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] normalizationHomogeneousSourceChartAlgebra

/-- Multiplication of ORIGINAL normalized homogeneous fractions, through
the ACTUAL normalization chart algebra action. -/
theorem normalizationHomogeneousChart_smul_fraction
    (a : R) (ha : a ∈ 𝒜 1)
    (haB : algebraMap R S a ∈ 𝓑 1)
    (d e : ℕ) (c : R) (hc : c ∈ 𝒜 d) (b : S) (hb : b ∈ 𝓑 e) :
    HomogeneousLocalization.Away.mk 𝒜 ha d c (by simpa using hc) •
      HomogeneousLocalization.Away.mk 𝓑 haB e b (by simpa using hb) =
    HomogeneousLocalization.Away.mk 𝓑 haB (d+e) (c • b)
      (by simpa using SetLike.GradedSMul.smul_mem hc hb) := by
  apply HomogeneousLocalization.val_injective
  rw [Algebra.smul_def,HomogeneousLocalization.val_mul]
  change (normalizationHomogeneousChartMap 𝒜 𝓑 a
      (HomogeneousLocalization.Away.mk 𝒜 ha d c (by simpa using hc))).val *
    (HomogeneousLocalization.Away.mk 𝓑 haB e b (by simpa using hb)).val = _
  rw [normalizationHomogeneousChartMap_mk 𝒜 𝓑 a ha d c hc,HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
    ← IsLocalization.mk'_mul]
  simp only [Algebra.smul_def,pow_add]
  congr 1

end LinearStudy
