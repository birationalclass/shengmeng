module
public import Linear.SchemeModuleHomUnitCurry
public import Linear.SchemeModuleHomOpenImmersionIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}
/-- Restrict SAME original curried functional along the ACTUAL open immersion,using the native structure-sheaf unit comparison. No section/class compatibility certificate is assumed. -/
theorem schemeModuleHomOpenImmersionIso_curry
    {M N : X.Modules} (j : Y ⟶ X) [IsOpenImmersion j] (a : M ⟶ N) :
    (Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map ((schemeModuleHomUnitAddEquiv M N).symm a) ≫
        (schemeModuleHomOpenImmersionIso M N j).hom =
      (schemeModuleHomUnitAddEquiv (M.restrict j) (N.restrict j)).symm
        ((Scheme.Modules.restrictFunctor j).map a) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro r
  apply Subtype.ext
  change (_ : (Over.forget W.unop).op ⋙ (M.restrict j).presheaf ⟶
    (Over.forget W.unop).op ⋙ (N.restrict j).presheaf) = _
  ext Z x
  change X.presheaf.map (j.opensFunctor.map Z.unop.hom).op
      ((j.appIso W.unop).inv r) • a.app (j ''ᵁ Z.unop.left) x =
    (j.appIso Z.unop.left).inv (Y.presheaf.map Z.unop.hom.op r) •
      a.app (j ''ᵁ Z.unop.left) x
  congr 1
  exact (congr($(j.appIso_inv_naturality Z.unop.hom.op) r)).symm
end LinearStudy
