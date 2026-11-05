module
public import Linear.NativeGradedBaseSourceChart
public import Linear.NormalizationChartScalarComparison
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
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑]
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar

/-- The comparison intertwines the genuine base chart scalar with the
genuine source chart scalar induced by the original normalization map. -/
theorem moduleBaseSourceLocalizationEquiv_chart_smul
    (a : R) (ha : a ∈ 𝒜 1) (c : HomogeneousLocalization.Away 𝒜 a)
    (x : LocalizedModule (Submonoid.powers a) M) :
    moduleBaseSourceLocalizationEquiv (S := S) a (c • x) =
      normalizationHomogeneousChartMap 𝒜 𝓑 a c •
        moduleBaseSourceLocalizationEquiv (S := S) a x := by
  obtain ⟨n,b,hb,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ha c
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    change moduleBaseSourceLocalizationEquiv (S := S) a
      ((HomogeneousLocalization.Away.mk 𝒜 ha n b hb).val • LocalizedModule.mk m s) =
      (normalizationHomogeneousChartMap 𝒜 𝓑 a
        (HomogeneousLocalization.Away.mk 𝒜 ha n b hb)).val • _
    rw [HomogeneousLocalization.Away.val_mk,LocalizedModule.mk_smul_mk,
      moduleBaseSourceLocalizationEquiv_mk,
      normalizationHomogeneousChartMap_mk 𝒜 𝓑 a ha n b
        (by simpa only [smul_eq_mul,mul_one] using hb),
      moduleBaseSourceLocalizationEquiv_mk,
      ← localizedModule_abstract_smul_eq_native (Submonoid.powers (algebraMap R S a)),
      LocalizedModule.mk'_smul_mk (Localization.Away (algebraMap R S a))]
    congr 1
    · exact (IsScalarTower.algebraMap_smul S b m).symm
    · apply Subtype.ext
      simp only [Submonoid.coe_mul,map_mul,map_pow]
end LinearStudy
