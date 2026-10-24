module
public import Linear.SchemeModuleGlobalExtActualHCohomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry
universe u
/-- Cache the ALREADY native actual-H additive group at an abstract scheme
and coefficient. This is exactly the existing instance;no new cohomology
model or mathematical assumption is introduced. -/
def schemeModuleActualCohomologyAddCommGroup (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    AddCommGroup (schemeModuleActualCohomology X M n) := inferInstance
end LinearStudy
