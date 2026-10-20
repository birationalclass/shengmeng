module
public import Linear.SchemeModuleSupportedRestrictionUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- For an ACTUAL scheme isomorphism,the native restriction-adjunction
unit is an isomorphism on every actual module sheaf. Derive it using
whole original range coverage,not a supplied unit-invertibility input. -/
theorem schemeModule_restrictionUnit_isIso_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    IsIso ((Scheme.Modules.restrictAdjunction f).unit.app M) := by
  apply schemeModule_restrictionUnit_isIso_of_originalCover f M (fun i : Empty => nomatch i)
  · intro y
    left
    rw [f.image_top_eq_opensRange,Scheme.Hom.opensRange_of_isIso]
    trivial
  · intro i
    exact nomatch i

/-- Native pushforward along the ACTUAL scheme isomorphism identifies
its original structure module with the original target structure module.
Use the SAME native unit and native restriction-of-unit isomorphism. -/
def schemeModulePushforwardUnitIsoOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pushforward e.hom).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf := by
  letI := schemeModule_restrictionUnit_isIso_of_isIso e.hom
    (SheafOfModules.unit Y.ringCatSheaf)
  exact (Scheme.Modules.pushforward e.hom).mapIso (Scheme.Modules.restrictUnitIso e.hom).symm ≪≫
    (asIso ((Scheme.Modules.restrictAdjunction e.hom).unit.app
      (SheafOfModules.unit Y.ringCatSheaf))).symm

/-- Push the ORIGINAL chart-cut structure sheaf into the original
ambient scheme,then compare with the WHOLE cut's actual closed map.
Scheme iso and original map-square inputs are EXPLICIT here;the original
geometric application constructs both rather than assuming them. -/
def schemeModuleOriginalCutStructurePushforwardIso {Z0 Z U X : Scheme.{u}}
    (e : Z0 ≅ Z) (q : Z0 ⟶ U) (j : U ⟶ X) (i : Z ⟶ X)
    (hsquare : e.hom ≫ i = q ≫ j) :
    (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pushforward q).obj
      (SheafOfModules.unit Z0.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
  (Scheme.Modules.pushforwardComp q j).app _ ≪≫
    (Scheme.Modules.pushforwardCongr hsquare.symm).app _ ≪≫
    (Scheme.Modules.pushforwardComp e.hom i).symm.app _ ≪≫
    (Scheme.Modules.pushforward i).mapIso (schemeModulePushforwardUnitIsoOfIso e)

end LinearStudy