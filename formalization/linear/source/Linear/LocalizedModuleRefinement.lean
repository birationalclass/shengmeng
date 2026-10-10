module
public import Linear.FiniteNativeCoextensionLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The ACTUAL module restriction to a finer original localization.
It is constructed using the localization universal property. -/
def originalLocalizedModuleRefinement (P T : Submonoid R) (hPT : P ≤ T) :
    LocalizedModule P M →ₗ[R] LocalizedModule T M :=
  LocalizedModule.lift P (LocalizedModule.mkLinearMap T M)
    (fun s => IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T M)
      ⟨s,hPT s.property⟩)

theorem originalLocalizedModuleRefinement_mk_one
    (P T : Submonoid R) (hPT : P ≤ T) (m : M) :
    originalLocalizedModuleRefinement (M := M) P T hPT (LocalizedModule.mk m 1) =
      LocalizedModule.mk m 1 :=
  LocalizedModule.lift_mk_one P (LocalizedModule.mkLinearMap T M) _ m

/-- Restriction keeps the original numerator and maps its ORIGINAL
denominator to the finer denominator submonoid. -/
theorem originalLocalizedModuleRefinement_mk
    (P T : Submonoid R) (hPT : P ≤ T) (m : M) (s : P) :
    originalLocalizedModuleRefinement (M := M) P T hPT (LocalizedModule.mk m s) =
      LocalizedModule.mk m (⟨s,hPT s.property⟩ : T) := by
  have hs : Function.Injective (fun x : LocalizedModule T M => (s : R) • x) := by
    exact ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T M)
        (⟨s,hPT s.property⟩ : T))).1
  apply hs
  have hsP : (s : R) • LocalizedModule.mk m s = LocalizedModule.mk m 1 := by
    simpa only [LocalizedModule.smul'_mk,Submonoid.smul_def] using
      LocalizedModule.mk_cancel s m
  have hsT : (s : R) • LocalizedModule.mk m (⟨s,hPT s.property⟩ : T) =
      LocalizedModule.mk m 1 := by
    simpa only [LocalizedModule.smul'_mk,Submonoid.smul_def] using
      LocalizedModule.mk_cancel (⟨s,hPT s.property⟩ : T) m
  change (s : R) • originalLocalizedModuleRefinement (M := M) P T hPT
      (LocalizedModule.mk m s) = (s : R) • LocalizedModule.mk m (⟨s,hPT s.property⟩ : T)
  rw [← (originalLocalizedModuleRefinement (M := M) P T hPT).map_smul,hsP,
    originalLocalizedModuleRefinement_mk_one,hsT]
end LinearStudy
