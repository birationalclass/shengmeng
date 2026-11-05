module
public import Linear.SchemeModuleActualHBaseScalars
public import Linear.SchemeModuleActualCohomologyGroup
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry
universe u

/-- Bundle the independently defined base-global-section module on the
original actual H group. -/
def originalActualHBaseModuleObject
    {X S : Scheme.{u}} (pi : X ⟶ S) (M : X.Modules) (n : ℕ) :
    ModuleCat.{u} Γ(S,⊤) :=
  @ModuleCat.of Γ(S,⊤) _ (schemeModuleActualCohomology X M n)
    (schemeModuleActualCohomologyAddCommGroup X M n)
    (schemeModuleActualHBaseModule pi M n)

end LinearStudy
#check LinearStudy.originalActualHBaseModuleObject
#print LinearStudy.originalActualHBaseModuleObject
#print axioms LinearStudy.originalActualHBaseModuleObject
