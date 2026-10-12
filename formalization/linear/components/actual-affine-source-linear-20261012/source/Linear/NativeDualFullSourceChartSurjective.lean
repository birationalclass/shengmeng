module
public import Linear.NormalizationChartNativeDualFraction
public import Linear.NormalizationSourceChartHomogeneousFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory
universe u
variable {K R S : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Module.Finite R S]
attribute [local instance] coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule nativeHomogeneousAwayModuleScalar
  LocalizedModule.moduleOfIsLocalization normalizationHomogeneousSourceChartAlgebra

/-- The ACTUAL native degree-zero dual comparison is surjective onto
linear functionals on the FULL ORIGINAL source chart. Its preimage is
constructed by homogenization and clearing one original denominator.
No finite-free source, canonical-sheaf model or dual-surjectivity premise
is supplied. Canonical identification and gluing remain separate. -/
theorem finiteNativeDualFullSourceChartMap_surjective
    (a : R) (ha : a ∈ 𝒜 1)
    (hinj : Function.Injective (algebraMap R (Localization.Away a))) :
    Function.Surjective (finiteNativeDualFullSourceChartMap 𝒜 𝓑 a ha hinj) := by
  intro f
  have haB : algebraMap R S a ∈ 𝓑 1 := by
    simpa only [Algebra.smul_def,mul_one,vadd_eq_add,add_zero] using
      SetLike.GradedSMul.smul_mem ha (SetLike.one_mem_graded 𝓑)
  obtain ⟨m,ell,hell,hval⟩ := normalizationChartFunctional_exists_native_dual_fraction
    𝒜 𝓑 a ha haB hinj f
  let sm : Submonoid.powers a := ⟨a^m,⟨m,rfl⟩⟩
  let z : nativeGradedModuleAwayZero 𝒜 (coextensionGradedPiece 𝒜 𝓑) a :=
    ⟨LocalizedModule.mk ell sm,Submodule.subset_span ⟨m,ell,hell,rfl⟩⟩
  refine ⟨z,?_⟩
  apply LinearMap.ext
  intro y
  apply HomogeneousLocalization.val_injective
  obtain ⟨n,b,hb,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝓑 haB y
  have hb' : b ∈ 𝓑 n := by simpa only [smul_eq_mul,mul_one] using hb
  let sn : Submonoid.powers a := ⟨a^n,⟨n,rfl⟩⟩
  let x : nativeNormalizationSourceAwayZero 𝒜 𝓑 a :=
    ⟨LocalizedModule.mk b sn,Submodule.subset_span ⟨n,b,hb',rfl⟩⟩
  have hx : (nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).symm
      (HomogeneousLocalization.Away.mk 𝓑 haB n b hb) = x := by
    apply (nativeNormalizationSourceChartEquiv 𝒜 𝓑 a ha).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (nativeNormalizationSourceChartEquiv_homogeneous_fraction
      𝒜 𝓑 a ha haB n b hb').symm
  rw [finiteNativeDualFullSourceChartMap_apply_val,hx]
  change finiteNativeCoextensionLocalizationEquiv (Q := Localization.Away a)
    (Submonoid.powers a) hinj (LocalizedModule.mk ell sm) (LocalizedModule.mk b sn) = _
  rw [finiteNativeCoextensionLocalizationEquiv_apply_fraction]
  apply (IsLocalization.map_units (Localization.Away a) (sm*sn)).mul_left_cancel
  rw [IsLocalization.mk'_spec']
  change algebraMap R (Localization.Away a) (ell b) =
    algebraMap R (Localization.Away a) ((sm : R)*(sn : R)) *
      (f (HomogeneousLocalization.Away.mk 𝓑 haB n b hb)).val
  simpa only [sm,sn,Submonoid.coe_mul,map_mul,map_pow,pow_add,mul_comm,mul_left_comm,
    mul_assoc] using hval n b hb'
end LinearStudy
