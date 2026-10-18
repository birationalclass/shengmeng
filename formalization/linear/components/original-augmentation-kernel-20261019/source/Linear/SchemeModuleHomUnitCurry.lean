module
public import Linear.SchemeModuleHomPostcompose
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}}

/-- ACTUAL global internal-Hom currying at the structure-sheaf unit.
Both sides retain actual original module-sheaf morphisms. -/
def schemeModuleHomUnitAddEquiv (P N : X.Modules) :
    (SheafOfModules.unit X.ringCatSheaf ⟶ schemeModuleHomModuleSheaf P N) ≃+ (P ⟶ N) where
  toEquiv := (SheafOfModules.unitHomEquiv (schemeModuleHomModuleSheaf P N)).trans
    (schemeModuleHomModuleGlobalEquiv P N)
  map_add' f g := by
    apply SheafOfModules.hom_ext
    ext U x
    rfl

/-- Coefficient postcomposition uses the SAME original actual currying. -/
theorem schemeModuleHomUnitAddEquiv_symm_postcompose (P : X.Modules)
    {M N : X.Modules} (f : P ⟶ M) (c : M ⟶ N) :
    (schemeModuleHomUnitAddEquiv P N).symm (f ≫ c) =
      (schemeModuleHomUnitAddEquiv P M).symm f ≫ schemeModuleHomPostcompose c := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ P.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf) = _
  ext W x
  change X.presheaf.map W.unop.hom.op r • c.app W.unop.left (f.app W.unop.left x) =
    c.app W.unop.left (X.presheaf.map W.unop.hom.op r • f.app W.unop.left x)
  exact (Scheme.Modules.Hom.app_smul c _ _).symm

end LinearStudy
