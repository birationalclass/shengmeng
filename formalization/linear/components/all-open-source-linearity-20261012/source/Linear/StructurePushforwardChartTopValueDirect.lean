module
public import Linear.StructurePushforwardChartIso
public import Linear.ModuleChartTransportComponents
public import Linear.StructureUnitMapValue
public import Linear.SchemeIsoTopPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1000000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y S T : Scheme.{u}}
attribute [local irreducible] structurePushforwardChartIso
theorem structurePushforwardChartTopValueDirect
    (f : X ⟶ Y) (U : Y.Opens)
    (a : ↑(f ⁻¹ᵁ U) ≅ S) (b : ↑U ≅ T) (g : S ⟶ T)
    (hsquare : (f ∣_ U) = a.hom ≫ g ≫ b.inv)
    (r : Γ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit X.ringCatSheaf),U)) :
    HEq ((structurePushforwardChartIso (X := X) (Y := Y) (S := S) (T := T)
      f U a b g hsquare).hom.app (⊤ : T.Opens)
      (((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)).presheaf.map
          (eqToHom (show (b.inv ≫ U.ι) ''ᵁ ⊤ = U by simp)).op r))
    (a.inv.appTop ((f ⁻¹ᵁ U).topIso.inv (show Γ(X,f ⁻¹ᵁ U) from r))) := by
  apply heq_of_eq
  simp only [structurePushforwardChartIso, schemeModuleChartPushforwardRestrictionIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv, Scheme.Modules.Hom.comp_app,
    schemeModuleRestrictMap_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply, AddCommGrpCat.id_apply,
    schemeModulePushforwardOpenRestrictionIso_hom_app,
    schemeModuleRestrictFunctorAdjCounitIso_hom_app,
    schemeModuleIsoPushforwardRestriction_hom_app,
    schemeModuleRestrictUnitIso_value, Scheme.Hom.preimage_top,
    Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  change ((a.inv ≫ (f ⁻¹ᵁ U).ι).appIso (⊤ : S.Opens)).hom
    (X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map _
      (X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map _
        (X.presheaf.map _ r))))))) =
    a.inv.appTop ((f ⁻¹ᵁ U).topIso.inv r)
  rw [Scheme.Hom.comp_appIso]
  dsimp only [Iso.trans_hom]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply, Functor.mapIso_hom]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  simp only [Category.comp_id]
  congr 1
  apply congrArg ConcreteCategory.hom
  erw [schemeIsoAppIsoTopHom a.symm]
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map,
    ← Category.assoc, ← Functor.map_comp]
  congr 1
end LinearStudy
