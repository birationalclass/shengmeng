module
public import Linear.LocalizedModuleRefinement
public import Linear.NativeLocalizationScalarComparison
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- Original module refinement is semilinear over the actual localization
ring map, for arbitrary inclusions of the original denominator sets. -/
theorem originalLocalizedModuleRefinement_smul
    (P T : Submonoid R) (hPT : P ≤ T) (c : Localization P)
    (x : LocalizedModule P M) :
    originalLocalizedModuleRefinement P T hPT (c • x) =
      IsLocalization.map (S := Localization P) (M := P) (T := T)
        (Localization T) (RingHom.id R) (fun _ hr => hPT hr) c •
        originalLocalizedModuleRefinement P T hPT x := by
  obtain ⟨⟨r,s⟩,hc⟩ := IsLocalization.mk'_surjective P c
  dsimp only at hc
  rw [← hc]
  induction x using LocalizedModule.induction_on with
  | _ m t =>
    rw [← localizedModule_abstract_smul_eq_native P,
      LocalizedModule.mk'_smul_mk (Localization P),
      originalLocalizedModuleRefinement_mk,
      IsLocalization.map_mk',originalLocalizedModuleRefinement_mk,
      ← localizedModule_abstract_smul_eq_native T,
      LocalizedModule.mk'_smul_mk (Localization T)]
    rfl
end LinearStudy
