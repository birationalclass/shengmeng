module
public import Linear.NormalizationWeightedSourceEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The arbitrary-degree source comparison retains the exact original
homogeneous fraction, including its actual numerator and denominator. -/
theorem nativeNormalizationWeightedSourceChartEquiv_homogeneous_fraction
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d) (haB : algebraMap R S a ∈ 𝓑 d)
    (n : ℕ) (b : S) (hb : b ∈ 𝓑 (n*d)) :
    nativeNormalizationWeightedSourceChartEquiv 𝒜 𝓑 d a ha
      ⟨LocalizedModule.mk b (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a),
        Submodule.subset_span ⟨n,b,by
          simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
            ite_true,Int.toNat_natCast] using hb,rfl⟩⟩ =
      HomogeneousLocalization.Away.mk 𝓑 haB n b
        (by simpa only [smul_eq_mul] using hb) := by
  apply HomogeneousLocalization.val_injective
  rw [nativeNormalizationWeightedSourceChartEquiv_val,nativeNormalizationFullChartEquiv_mk,
    HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap R S) a n
end LinearStudy
