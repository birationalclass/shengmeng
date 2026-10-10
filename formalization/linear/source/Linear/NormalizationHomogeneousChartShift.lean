module
public import Linear.NormalizationSourceChartLinearMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]

/-- Increasing both the actual homogeneous numerator and denominator by
the SAME original denominator power preserves the full chart element. -/
theorem normalizationHomogeneousChart_shift_fraction
    (a : R) (haB : algebraMap R S a ∈ 𝓑 1)
    (n k : ℕ) (b : S) (hb : b ∈ 𝓑 n) :
    HomogeneousLocalization.Away.mk 𝓑 haB (n+k)
      ((algebraMap R S a)^k * b)
      (by simpa [add_comm] using
        SetLike.mul_mem_graded (SetLike.pow_mem_graded k haB) hb) =
    HomogeneousLocalization.Away.mk 𝓑 haB n b (by simpa using hb) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk,HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk']
  let den (l : ℕ) : Submonoid.powers (algebraMap R S a) := ⟨_,⟨l,rfl⟩⟩
  change IsLocalization.mk' (Localization.Away (algebraMap R S a))
    ((algebraMap R S a)^k*b) (den (n+k)) =
    IsLocalization.mk' (Localization.Away (algebraMap R S a)) b (den n)
  have hden : den (n+k) = den n * den k := by
    apply Subtype.ext
    exact pow_add _ _ _
  rw [hden,mul_comm ((algebraMap R S a)^k) b]
  exact IsLocalization.mk'_cancel b (den n) (den k)

end LinearStudy
