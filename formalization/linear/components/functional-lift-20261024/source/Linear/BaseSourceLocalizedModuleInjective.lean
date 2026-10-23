module
public import Linear.NativeProjectiveChartSectionsInjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Further base localization is injective when its denominators have
nonzero images in the integral source. This only needs torsion-freeness
over the source, which includes a quotient ring as its own module. -/
theorem originalLocalizedModuleRefinement_injective_source_torsionFree
    [IsDomain S] [Module.IsTorsionFree S M]
    (P T : Submonoid R) (hPT : P ≤ T)
    (hT : ∀ t ∈ T, algebraMap R S t ≠ 0) :
    Function.Injective (originalLocalizedModuleRefinement (M := M) P T hPT) := by
  apply IsLocalizedModule.injective_of_map_zero P (LocalizedModule.mkLinearMap P M)
  intro m hm
  change originalLocalizedModuleRefinement P T hPT (LocalizedModule.mk m 1) = 0 at hm
  rw [originalLocalizedModuleRefinement_mk_one] at hm
  have hz : LocalizedModule.mkLinearMap T M m = 0 := hm
  obtain ⟨t,ht⟩ := (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T M)).mp hz
  change (t : R) • m = 0 at ht
  have htS : algebraMap R S (t : R) • m = 0 := by
    simpa only [IsScalarTower.algebraMap_smul] using ht
  have hm0 : m = 0 := (smul_eq_zero_iff_right (hT t.val t.property)).mp htS
  simp [hm0]

/-- A coordinate whose source image is zero annihilates the SAME original
module. Its actual base-localized module is therefore zero as well. -/
theorem baseSourceAway_subsingleton_of_image_zero
    (a : R) (ha : algebraMap R S a = 0) :
    Subsingleton (LocalizedModule (Submonoid.powers a) M) := by
  apply (LocalizedModule.subsingleton_iff (S := Submonoid.powers a)).mpr
  intro m
  refine ⟨a,Submonoid.mem_powers a,?_⟩
  rw [← IsScalarTower.algebraMap_smul S a m,ha,zero_smul]
end LinearStudy
