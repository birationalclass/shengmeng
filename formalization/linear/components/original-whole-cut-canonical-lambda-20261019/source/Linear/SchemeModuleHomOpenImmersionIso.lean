module
public import Linear.SchemeModuleHomOpenImmersionMorphism
public import Linear.SchemeModuleHomOpenImmersionBijective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (M N : X.Modules)
variable (j : Y ⟶ X) [IsOpenImmersion j]

/-- Restriction of the actual global internal Hom is isomorphic to
the actual internal Hom of the SAME restricted modules. Every component
is the original restriction map, with its bijectivity independently proved. -/
def schemeModuleHomOpenImmersionIso :
    (schemeModuleHomModuleSheaf M N).restrict j ≅
      schemeModuleHomModuleSheaf (M.restrict j) (N.restrict j) := by
  let η := schemeModuleHomOpenImmersionMorphism M N j
  haveI : IsIso η := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr (fun W => by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact schemeModuleHomOpenImmersionRestrictSection_bijective M N j W)
  exact asIso η
end LinearStudy
