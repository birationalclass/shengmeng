module
public import Linear.NormalizationWeightedSourceMembership
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
  LocalizedModule.moduleOfIsLocalization

/-- Every actual full degree-zero source chart fraction comes from
the ORIGINAL generated source chart module. No choice of a chart model
or canonical module is an input. -/
theorem nativeNormalizationWeightedSourceAwayZero_surjective
    (d : ℕ) (a : R) (ha : a ∈ 𝒜 d)
    (z : HomogeneousLocalization.Away 𝓑 (algebraMap R S a)) :
    ∃ x : nativeGradedModuleAwayDegreeZero 𝒜 (nativeProjectiveRingIntegerPiece 𝓑) d a,
      nativeNormalizationFullChartEquiv (S := S) a x.val = z.val := by
  have haB : algebraMap R S a ∈ 𝓑 d := by
    simpa only [Algebra.smul_def,mul_one,vadd_eq_add,add_zero] using
      SetLike.GradedSMul.smul_mem ha (SetLike.one_mem_graded 𝓑)
  obtain ⟨n,b,hb,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝓑 haB z
  have hb' : b ∈ 𝓑 (n*d) := by simpa only [smul_eq_mul,mul_one] using hb
  let s : Submonoid.powers a := ⟨a^n,⟨n,rfl⟩⟩
  refine ⟨⟨LocalizedModule.mk b s,Submodule.subset_span ⟨n,b,by
      simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
        ite_true,Int.toNat_natCast] using hb',rfl⟩⟩,?_⟩
  rw [nativeNormalizationFullChartEquiv_mk,
    HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
  congr 1
  apply Subtype.ext
  exact map_pow (algebraMap R S) a n

end LinearStudy
