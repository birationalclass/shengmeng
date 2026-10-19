module
public import Linear.SchemeModuleGlobalToInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- Compute actual descended map on any SAME actual injective cocycle,
without unfolding its quotient presentation during geometric comparisons. -/
theorem schemeModuleGlobalToInternalExtViaResolution_cocycle {X : Scheme.{u}}
    {N : X.Modules} (I : InjectiveResolution N) (P : X.Modules) (n : ℕ)
    (f : injectiveCocycleGroup I P (n+1)) :
    schemeModuleGlobalToInternalExtViaResolution I P n (injectiveCocycleExtMap I P (n+1) f) =
      schemeModuleInjectiveCocycleToInternalExt I P (n+1) f :=
  schemeModuleGlobalToInternalExtViaResolution_extMk I P n f.val f.property
end LinearStudy
