module
public import Linear.SchemeModuleHomPresheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Restrict an actual local O-linear morphism using mathlib's original
Over functor and its proved comparison isomorphisms. -/
def schemeModuleHomRestrict {U V : X.Opens} (i : V ⟶ U)
    (f : M.over U ⟶ N.over U) : M.over V ⟶ N.over V :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app M) ≫
    (SheafOfModules.overMap X.ringCatSheaf i).map f ≫
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N)

/-- The local O-linear Hom correspondence commutes with the ACTUAL
module restriction functors, including their comparison isomorphisms. -/
theorem schemeModuleHomOverEquiv_restrict {U V : X.Opens} (i : V ⟶ U)
    (f : M.over U ⟶ N.over U) :
    schemeModuleHomOverEquiv M N V (schemeModuleHomRestrict M N i f) =
      (schemeModuleHomPresheaf M N).map i.op (schemeModuleHomOverEquiv M N U f) := by
  apply Subtype.ext
  change (_ : (Over.forget V).op ⋙ M.presheaf ⟶ (Over.forget V).op ⋙ N.presheaf) = _
  ext W x
  rfl

end LinearStudy
