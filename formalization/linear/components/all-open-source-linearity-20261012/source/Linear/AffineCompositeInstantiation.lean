module
public import Linear.SchemeModuleHomCompositeRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 150000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

def affineCompositeInstantiation (U : X.Opens) (R : CommRingCat.{u}) (e : ↑U ≅ Spec R)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) :=
  @schemeModuleHomCompositeRestriction X (Spec R) M N U e.inv
    (inferInstanceAs (IsOpenImmersion e.inv)) h

end LinearStudy
