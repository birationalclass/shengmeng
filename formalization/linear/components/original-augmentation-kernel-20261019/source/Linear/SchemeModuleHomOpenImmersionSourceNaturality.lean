module
public import Linear.SchemeModuleHomOpenImmersionIso
public import Linear.SchemeModuleHomPrecompose
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
/-- The ACTUAL original internal-Hom open-immersion comparison preserves SAME source precomposition. This is the differential square needed to restrict the whole top Hom cokernel. -/
theorem schemeModuleHomOpenImmersionIso_precompose
    {M' M : X.Modules} (N : X.Modules) (j : Y ⟶ X) [IsOpenImmersion j] (a : M' ⟶ M) :
    (Scheme.Modules.restrictFunctor j).map (schemeModuleHomPrecompose (N := N) a) ≫
        (schemeModuleHomOpenImmersionIso M' N j).hom =
      (schemeModuleHomOpenImmersionIso M N j).hom ≫
        schemeModuleHomPrecompose (N := N.restrict j) ((Scheme.Modules.restrictFunctor j).map a) := by
  apply SheafOfModules.hom_ext
  ext W f
  apply Subtype.ext
  change (_ : (Over.forget W.unop).op ⋙ (M'.restrict j).presheaf ⟶
    (Over.forget W.unop).op ⋙ (N.restrict j).presheaf) = _
  ext Z x
  rfl
end LinearStudy
