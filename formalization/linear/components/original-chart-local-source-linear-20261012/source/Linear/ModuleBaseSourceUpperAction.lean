module
public import Linear.ModuleBaseSourceLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
universe u
variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The actual base/source localization comparison preserves ORIGINAL
upper-ring multiplication, localized by its universal linear map. -/
theorem moduleBaseSourceLocalizationEquiv_upper_action (a : R) (s : S)
    (x : LocalizedModule (Submonoid.powers a) M) :
    moduleBaseSourceLocalizationEquiv (S := S) a
      (IsLocalizedModule.map (Submonoid.powers a)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
        (DistribSMul.toLinearMap R M s) x) =
      s • moduleBaseSourceLocalizationEquiv (S := S) a x := by
  induction x using LocalizedModule.induction_on with
  | _ m p =>
    rw [IsLocalizedModule.map_LocalizedModules,
      moduleBaseSourceLocalizationEquiv_mk,
      moduleBaseSourceLocalizationEquiv_mk, LocalizedModule.smul'_mk]
    rfl

end LinearStudy
