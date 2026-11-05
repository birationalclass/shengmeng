module
public import Linear.SchemeModuleActualHObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- This is an equality of the SAME actual H group object with its
ORIGINAL Ext presentation,not a chosen mathematical duality. -/
theorem schemeModuleActualHObject_eq_ofCohomology
    (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    schemeModuleActualHObject X M n = AddCommGrpCat.of (schemeModuleActualCohomology X M n) := rfl
end LinearStudy
