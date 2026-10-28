module
public import Linear.LocalizedModuleRefinement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
/-- Actual original localization restriction is natural for every
ORIGINAL coefficient map;both sides keep the same numerator and denominator. -/
theorem originalLocalizedModuleRefinement_map (P T : Submonoid R) (hPT : P ≤ T)
    (f : M →ₗ[R] N) (x : LocalizedModule P M) :
    LocalizedModule.map T f (originalLocalizedModuleRefinement P T hPT x) =
      originalLocalizedModuleRefinement P T hPT (LocalizedModule.map P f x) := by
  induction x using LocalizedModule.induction_on with
  | h m b => simp only [originalLocalizedModuleRefinement_mk,LocalizedModule.map_mk]
end LinearStudy
