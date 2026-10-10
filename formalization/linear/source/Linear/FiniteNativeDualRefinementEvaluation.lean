module
public import Linear.LocalizedModuleRefinement
public import Linear.NativeDualLocalizationFractionValues
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable [Algebra R S] [Module.Finite R S]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Restriction of the ACTUAL native finite dual commutes with evaluation
on the ACTUAL localized source. Both original denominators are retained.
No chart compatibility, finite-free presentation or canonical model is assumed. -/
theorem finiteNativeDual_refinement_evaluation
    (P T : Submonoid R) (hPT : P ≤ T)
    (hP : Function.Injective (algebraMap R (Localization P)))
    (hT : Function.Injective (algebraMap R (Localization T)))
    (ell : LocalizedModule P ((ModuleCat.restrictScalars (algebraMap R S)).obj
      ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))))
    (x : LocalizedModule P S) :
    finiteNativeCoextensionLocalizationEquiv (Q := Localization T) T hT
      (originalLocalizedModuleRefinement P T hPT ell)
      (originalLocalizedModuleRefinement P T hPT x) =
      IsLocalization.map (S := Localization P) (M := P) (T := T)
        (Localization T) (RingHom.id R) (fun _ hr => hPT hr)
        (finiteNativeCoextensionLocalizationEquiv (Q := Localization P) P hP ell x) := by
  induction ell using LocalizedModule.induction_on with
  | _ ell s =>
    induction x using LocalizedModule.induction_on with
    | _ x t =>
      rw [originalLocalizedModuleRefinement_mk,
        originalLocalizedModuleRefinement_mk,
        finiteNativeCoextensionLocalizationEquiv_apply_fraction,
        finiteNativeCoextensionLocalizationEquiv_apply_fraction,
        IsLocalization.map_mk']
      rfl

end LinearStudy
