module
public import Linear.SchemeModulePushforwardOpenRestriction
public import Linear.SchemeModuleIsoPushforwardRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y S T : Scheme.{u}}

/-- Transport the ACTUAL global pushforward to specified source and target
affine chart isomorphisms. All maps are built from the original square;
no module-sheaf comparison is supplied as an assumption. -/
def schemeModuleChartPushforwardRestrictionIso
    (f : X ⟶ Y) (U : Y.Opens)
    (a : ↑(f ⁻¹ᵁ U) ≅ S) (b : ↑U ≅ T) (g : S ⟶ T)
    (hsquare : (f ∣_ U) = a.hom ≫ g ≫ b.inv) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict (b.inv ≫ U.ι) ≅
      (Scheme.Modules.pushforward g).obj
        (M.restrict (a.inv ≫ (f ⁻¹ᵁ U).ι)) := by
  let N := M.restrict (f ⁻¹ᵁ U).ι
  let Rb := Scheme.Modules.restrictFunctor b.inv
  exact (Scheme.Modules.restrictFunctorComp b.inv U.ι).app _ ≪≫
    Rb.mapIso (schemeModulePushforwardOpenRestrictionIso f U M) ≪≫
    Rb.mapIso ((Scheme.Modules.pushforwardCongr hsquare).app N) ≪≫
    Rb.mapIso ((Scheme.Modules.pushforwardComp a.hom (g ≫ b.inv)).symm.app N) ≪≫
    Rb.mapIso ((Scheme.Modules.pushforwardComp g b.inv).symm.app
      ((Scheme.Modules.pushforward a.hom).obj N)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso b.inv).app _ ≪≫
    (Scheme.Modules.pushforward g).mapIso
      ((schemeModuleIsoPushforwardRestriction a).app N) ≪≫
    (Scheme.Modules.pushforward g).mapIso
      ((Scheme.Modules.restrictFunctorComp a.inv (f ⁻¹ᵁ U).ι).symm.app M)

end LinearStudy
