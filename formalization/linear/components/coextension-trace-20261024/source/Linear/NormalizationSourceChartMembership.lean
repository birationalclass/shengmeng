module
public import Linear.NormalizationChartScalarComparison
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

/-- Every element of the ORIGINAL generated source degree-zero chart
maps into the actual full homogeneous Proj chart ring. -/
theorem nativeNormalizationSourceAwayZero_value
    (a : R) (ha : a ∈ 𝒜 1)
    (x : LocalizedModule (Submonoid.powers a) S)
    (hx : x ∈ nativeNormalizationSourceAwayZero 𝒜 𝓑 a) :
    ∃ z : HomogeneousLocalization.Away 𝓑 (algebraMap R S a),
      z.val = nativeNormalizationFullChartEquiv (S := S) a x := by
  have haB : algebraMap R S a ∈ 𝓑 1 := by
    simpa only [Algebra.smul_def,mul_one,vadd_eq_add,add_zero] using
      SetLike.GradedSMul.smul_mem ha (SetLike.one_mem_graded 𝓑)
  change x ∈ Submodule.span (HomogeneousLocalization.Away 𝒜 a) _ at hx
  refine Submodule.span_induction (R := HomogeneousLocalization.Away 𝒜 a)
    (p := fun x _ =>
    ∃ z : HomogeneousLocalization.Away 𝓑 (algebraMap R S a),
      z.val = nativeNormalizationFullChartEquiv (S := S) a x) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨n,b,hb,rfl⟩
    refine ⟨HomogeneousLocalization.Away.mk 𝓑 haB n b
      (by simpa only [smul_eq_mul,mul_one] using hb), ?_⟩
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
      nativeNormalizationFullChartEquiv_mk]
    congr 1
    apply Subtype.ext
    simp only [map_pow]
  · exact ⟨0,by simp⟩
  · intro y z hy hz iy iz
    obtain ⟨c,hc⟩ := iy
    obtain ⟨d,hd⟩ := iz
    refine ⟨c+d, ?_⟩
    simpa only [map_add,HomogeneousLocalization.val_add,hc,hd]
  · intro c y hy iy
    obtain ⟨z,hz⟩ := iy
    refine ⟨normalizationHomogeneousChartMap 𝒜 𝓑 a c * z, ?_⟩
    rw [HomogeneousLocalization.val_mul,hz,
      nativeNormalizationFullChartEquiv_chart_smul 𝒜 𝓑 a ha]

end LinearStudy
