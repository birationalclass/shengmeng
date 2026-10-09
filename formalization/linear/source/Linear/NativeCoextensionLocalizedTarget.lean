module
public import Linear.FiniteNativeCoextensionLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]
variable [Algebra R S] [Algebra R Q] [Module.Finite R S]
variable (P : Submonoid R) [IsLocalization P Q]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Compare the actual localized original native dual with the ACTUAL
native coextension after base localization. The target is mathlib's
original change-of-rings object, with its restricted base-ring action. -/
def finiteNativeCoextensionLocalizedTargetEquiv
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    LocalizedModule P ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))) ≃ₗ[Q]
      ((ModuleCat.restrictScalars (algebraMap Q S')).obj
        ((ModuleCat.coextendScalars (algebraMap Q S')).obj (ModuleCat.of Q Q))) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  exact (finiteNativeCoextensionLocalizationEquiv (R := R) (S := S) P hinj).trans
    (nativeCoextensionOriginalDualEquiv (R := Q) (S := S')).symm

/-- The native-target comparison preserves every original evaluation. -/
theorem finiteNativeCoextensionLocalizedTargetEquiv_apply_original
    (hinj : Function.Injective (algebraMap R Q)) :
    let S' := LocalizedModule P S
    letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
    letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
    ∀ ell : (ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)), ∀ x : S,
      nativeCoextensionOriginalDualEquiv (R := Q) (S := S')
        (finiteNativeCoextensionLocalizedTargetEquiv (S := S) P hinj
          (LocalizedModule.mk ell 1)) (LocalizedModule.mk x 1) =
            algebraMap R Q (nativeCoextensionOriginalDualEquiv (R := R) (S := S) ell x) := by
  let S' := LocalizedModule P S
  letI : Module Q S' := LocalizedModule.moduleOfIsLocalization
  letI : Algebra Q S' := LocalizedModule.algebraOfIsLocalization (S := P) Q
  dsimp only
  intro ell x
  simpa only [finiteNativeCoextensionLocalizedTargetEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply] using
      finiteNativeCoextensionLocalizationEquiv_apply_mk P hinj ell x

end LinearStudy
