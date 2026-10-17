module
public import Linear.SchemeModuleInternalExtZero
public import Linear.SchemeModuleHomUnitCurry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- The actual degree-zero global-to-internal Ext map on actual sheaf morphisms. -/
def schemeModuleHomToInternalExtZero (P N : X.Modules) :
    (P ⟶ N) →+ (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleInternalExt P N 0) where
  toFun a := (schemeModuleHomUnitAddEquiv P N).symm a ≫
    ((schemeModuleInternalExtZeroIso P).app N).inv
  map_zero' := by rw [map_zero,zero_comp]
  map_add' a b := by rw [map_add,Preadditive.add_comp]
end LinearStudy
