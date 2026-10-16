module
public import Linear.SchemeModuleHomModuleSheaf
public import Linear.SchemeModuleHomGlobal
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

/-- Actual sections of the constructed internal Hom MODULE sheaf are
exactly original local morphisms of sheaves of O-modules. -/
def schemeModuleHomModuleSectionsEquiv (U : X.Opens) :
    Γ(schemeModuleHomModuleSheaf M N,U) ≃ (M.over U ⟶ N.over U) :=
  (schemeModuleHomOverEquiv M N U).symm

/-- The actual module-sheaf restriction agrees with the original Over
restriction functor, retaining the mathlib comparison isomorphisms. -/
theorem schemeModuleHomModuleSectionsEquiv_restrict {U V : X.Opens} (i : V ⟶ U)
    (f : Γ(schemeModuleHomModuleSheaf M N,U)) :
    schemeModuleHomModuleSectionsEquiv M N V
      ((schemeModuleHomModuleSheaf M N).presheaf.map i.op f) =
    schemeModuleHomRestrict M N i (schemeModuleHomModuleSectionsEquiv M N U f) := by
  apply (schemeModuleHomOverEquiv M N V).injective
  change (schemeModuleHomOverEquiv M N V)
      ((schemeModuleHomOverEquiv M N V).symm
        ((schemeModuleHomPresheaf M N).map i.op f)) = _
  rw [Equiv.apply_symm_apply, schemeModuleHomOverEquiv_restrict]
  change (schemeModuleHomPresheaf M N).map i.op f =
    (schemeModuleHomPresheaf M N).map i.op
      ((schemeModuleHomOverEquiv M N U) ((schemeModuleHomOverEquiv M N U).symm f))
  rw [Equiv.apply_symm_apply]

/-- All actual global sections of the constructed internal Hom MODULE
sheaf correspond to actual global original O-module morphisms. -/
def schemeModuleHomModuleGlobalEquiv :
    (schemeModuleHomModuleSheaf M N).val.sections ≃ (M ⟶ N) :=
  schemeModuleHomGlobalEquiv M N

end LinearStudy
