module
public import Linear.StructureModuleCompositeChartValue
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
theorem schemeModuleRestrictUnitIso_value
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (W : X.Opens) (r : Γ(Y,f ''ᵁ W)) :
    (Scheme.Modules.restrictUnitIso f).hom.app W r =
    (f.appIso W).hom r := by
  rfl
end LinearStudy
