module
public import Linear.LocalizedModuleRefinement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Actual restriction preserves identity, as a linear-map equality. -/
theorem originalLocalizedModuleRefinement_refl (P : Submonoid R) :
    originalLocalizedModuleRefinement (M := M) P P le_rfl = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    rw [originalLocalizedModuleRefinement_mk]
    rfl

/-- Actual restrictions compose on the original modules, retaining the
same numerators and denominators. This is the cocycle law for refinement. -/
theorem originalLocalizedModuleRefinement_comp
    (P T U : Submonoid R) (hPT : P ≤ T) (hTU : T ≤ U) :
    (originalLocalizedModuleRefinement (M := M) T U hTU).comp
      (originalLocalizedModuleRefinement P T hPT) =
        originalLocalizedModuleRefinement P U (hPT.trans hTU) := by
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    change originalLocalizedModuleRefinement T U hTU
        (originalLocalizedModuleRefinement P T hPT (LocalizedModule.mk m s)) = _
    rw [originalLocalizedModuleRefinement_mk,originalLocalizedModuleRefinement_mk,
      originalLocalizedModuleRefinement_mk]

end LinearStudy
