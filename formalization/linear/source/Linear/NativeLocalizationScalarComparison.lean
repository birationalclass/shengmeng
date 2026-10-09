module
public import Mathlib.RingTheory.Localization.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (P : Submonoid R)

/-- The actual native Ore-localization scalar structure. -/
@[instance_reducible] def nativeLocalizedModuleScalar :
    Module (Localization P) (LocalizedModule P M) := OreLocalization.instModule

/-- The abstract-localization module action agrees with the native
Ore action at the actual full localization; this is proved on fractions. -/
theorem localizedModule_abstract_smul_eq_native :
    ∀ c : Localization P, ∀ x : LocalizedModule P M,
      @HSMul.hSMul (Localization P) (LocalizedModule P M)
        (LocalizedModule P M)
        (@instHSMul _ _ (show SMul (Localization P) (LocalizedModule P M) from
          LocalizedModule.smulOfIsLocalization (Localization P))) c x =
      @HSMul.hSMul (Localization P) (LocalizedModule P M)
        (LocalizedModule P M)
        (@instHSMul _ _ (nativeLocalizedModuleScalar (M := M) P).toSMul) c x := by
  letI : SMul (Localization P) (LocalizedModule P M) :=
    LocalizedModule.smulOfIsLocalization (Localization P)
  intro c x
  obtain ⟨⟨r,s⟩,hc⟩ := IsLocalization.mk'_surjective P c
  rw [← Localization.mk_eq_mk'] at hc
  subst c
  induction x using LocalizedModule.induction_on with
  | h m t =>
      calc
        (Localization.mk r s : Localization P) • LocalizedModule.mk m t =
            LocalizedModule.mk (r • m) (s*t) := by
          rw [Localization.mk_eq_mk']
          exact LocalizedModule.mk'_smul_mk (Localization P) r m s t
        _ = _ := (LocalizedModule.mk_smul_mk r m s t).symm

end LinearStudy
