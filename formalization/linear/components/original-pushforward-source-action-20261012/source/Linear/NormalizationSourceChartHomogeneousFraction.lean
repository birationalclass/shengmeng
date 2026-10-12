module
public import Linear.NativeDualFullSourceChartComparison
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
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The ACTUAL source-chart equivalence sends the original homogeneous
module fraction to the identical original homogeneous ring fraction. -/
theorem nativeNormalizationSourceChartEquiv_homogeneous_fraction
    (a : R) (ha : a ∈ 𝒜 1) (haB : algebraMap R S a ∈ 𝓑 1)
    (n : ℕ) (b : S) (hb : b ∈ 𝓑 n) :
    nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha
      ⟨LocalizedModule.mk b (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a),
        Submodule.subset_span ⟨n,b,hb,rfl⟩⟩ =
      HomogeneousLocalization.Away.mk 𝓑 haB n b (by simpa using hb) := by
  apply HomogeneousLocalization.val_injective
  rw [nativeNormalizationSourceChartEquiv_val,nativeNormalizationFullChartEquiv_mk,
    HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap R S) a n
end LinearStudy
