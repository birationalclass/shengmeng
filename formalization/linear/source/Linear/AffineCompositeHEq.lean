module
public import Linear.AffineCompositeInstantiation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 200000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M N : X.Modules)
theorem affineCompositeHEq (U : X.Opens) (R : CommRingCat.{u}) (e : ↑U ≅ Spec R)
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    HEq (schemeModuleHomAffineChartSectionsEquiv M N U R e h)
      (affineCompositeInstantiation M N U R e h) := by
  rfl
end LinearStudy
