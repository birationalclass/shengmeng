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

theorem schemeModulePushforwardOpenRestrictionIso_hom_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules)
    (W : (U : Scheme).Opens) :
    (schemeModulePushforwardOpenRestrictionIso f U M).hom.app W =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U W)).op := by
  rfl

theorem schemeModuleRestrictFunctorAdjCounitIso_hom_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules)
    (W : X.Opens) :
    ((Scheme.Modules.restrictFunctorAdjCounitIso f).hom.app M).app W =
      M.presheaf.map (eqToHom (f.preimage_image_eq W).symm).op := by
  rfl

theorem schemeModuleRestrictFunctorAdjCounitIso_inv_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : X.Modules)
    (W : X.Opens) :
    ((Scheme.Modules.restrictFunctorAdjCounitIso f).inv.app M).app W =
      M.presheaf.map (eqToHom (f.preimage_image_eq W)).op := by
  rfl

theorem schemeModuleRestrictMap_app {A B : Scheme.{u}} (q : A ⟶ B) [IsOpenImmersion q]
    {M N : B.Modules} (k : M ⟶ N) (W : A.Opens) :
    ((Scheme.Modules.restrictFunctor q).map k).app W = k.app (q ''ᵁ W) := by
  rfl

theorem schemeModuleIsoPushforwardRestriction_hom_app
    {X Y : Scheme.{u}} (e : X ≅ Y) (M : X.Modules) (W : Y.Opens) :
    ((schemeModuleIsoPushforwardRestriction e).hom.app M).app W =
      M.presheaf.map (eqToHom (Scheme.Hom.inv_image e W)).op := by
  ext x
  dsimp [schemeModuleIsoPushforwardRestriction]
  simp only [schemeModuleRestrictMap_app, Scheme.Modules.pushforwardId_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforwardComp_hom_app_app,
    schemeModuleRestrictFunctorAdjCounitIso_inv_app, ConcreteCategory.id_apply]
  change M.presheaf.map _ (M.presheaf.map _ x) = M.presheaf.map _ x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl


end LinearStudy
