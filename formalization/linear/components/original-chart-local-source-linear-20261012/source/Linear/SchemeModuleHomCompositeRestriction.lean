module
public import Linear.SchemeModuleHomRestrictionTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
variable (f : Y ⟶ (U : Scheme)) [IsOpenImmersion f]

/-- The actual composite restriction form of the original open Hom map. -/
def schemeModuleHomCompositeRestriction
    (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    M.restrict (f ≫ U.ι) ⟶ N.restrict (f ≫ U.ι) :=
  ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app M).inv ≫
    (Scheme.Modules.restrictFunctor f).map
      (schemeModuleHomOpenSectionsEquiv M N U h) ≫
    ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app N).hom

theorem schemeModuleHomCompositeRestriction_smul
    (r : Γ(X,U)) (h : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomCompositeRestriction M N U f (r • h) =
      schemeModuleHomCompositeRestriction M N U f h ≫
        originalGlobalModuleScalar (X := Y) (f.appTop (U.topIso.inv r))
          (N.restrict (f ≫ U.ι)) := by
  exact schemeModuleHomRestrictionTransport_smul M N U f
    ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app M)
    ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app N) r h

theorem schemeModuleHomCompositeRestriction_add
    (h k : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomCompositeRestriction M N U f (h + k) =
      schemeModuleHomCompositeRestriction M N U f h +
      schemeModuleHomCompositeRestriction M N U f k := by
  exact schemeModuleHomRestrictionTransport_add M N U f
    ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app M)
    ((Scheme.Modules.restrictFunctorComp f U.ι).symm.app N) h k

end LinearStudy
