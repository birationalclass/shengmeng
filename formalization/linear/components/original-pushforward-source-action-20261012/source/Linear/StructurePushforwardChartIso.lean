module
public import Linear.SchemeModuleChartPushforwardRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y S T : Scheme.{u}}
def structurePushforwardChartIso
    (f : X ⟶ Y) (U : Y.Opens)
    (a : ↑(f ⁻¹ᵁ U) ≅ S) (b : ↑U ≅ T) (g : S ⟶ T)
    (hsquare : (f ∣_ U) = a.hom ≫ g ≫ b.inv) :
    ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf)).restrict (b.inv ≫ U.ι) ≅
    (Scheme.Modules.pushforward g).obj (SheafOfModules.unit S.ringCatSheaf) :=
  schemeModuleChartPushforwardRestrictionIso f U a b g hsquare
    (SheafOfModules.unit X.ringCatSheaf) ≪≫
      (Scheme.Modules.pushforward g).mapIso
        (Scheme.Modules.restrictUnitIso (a.inv ≫ (f ⁻¹ᵁ U).ι))
end LinearStudy
