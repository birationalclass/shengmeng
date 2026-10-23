module
public import Linear.SchemeModuleGlobalToInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

set_option maxHeartbeats 400000
/-- SAME actual cocycle map with its native injective-comparison inverse. -/
theorem schemeModuleInjectiveCocycleToInternalExt_apply {N : X.Modules}
    (I : InjectiveResolution N) (P : X.Modules) (q : ℕ) (a : injectiveCocycleGroup I P q) :
    schemeModuleInjectiveCocycleToInternalExt I P q a =
      schemeModuleInjectiveInternalHomClassMap I P q a ≫
        (schemeModuleInternalExtInjectiveResolutionIso P N q I).inv := rfl

end LinearStudy
