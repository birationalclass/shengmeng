module
public import Linear.OriginalSourceScalarRecoveryInverse
public import Linear.PushforwardHomSourceScalarRecovery
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 180000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}
attribute [local irreducible] schemeModuleHomModuleSheaf

/-- The inverse actual Hom scalar recovery fixes EVERY original section. -/
theorem schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso_inv_apply
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    (schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso f N).inv.val.app (op U) h =
      (show Γ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
        (schemePushforwardHomSourceModuleSheaf f N),U) from h) := by
  let H := schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
  let R := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
  letI (W : Y.Opensᵒᵖ) : Module (R.obj.obj W) (H.val.presheaf.obj W) :=
    schemePushforwardHomSourceModule f N W.unop
  have hres : ∀ ⦃V W : Y.Opensᵒᵖ⦄ (i : V ⟶ W) (b : R.obj.obj V)
      (x : H.val.presheaf.obj V),
      H.val.presheaf.map i (b • x) = R.obj.map i b • H.val.presheaf.map i x := by
    intro V W i b x
    exact schemePushforwardHomSourceActionSection_restrict f N i.unop b x
  have hbase : ∀ (W : Y.Opensᵒᵖ) (r : Y.ringCatSheaf.obj.obj W)
      (x : H.val.presheaf.obj W),
      (show R.obj.obj W from f.toRingCatSheafHom.hom.app W r) • x = r • x := by
    intro W r x
    exact schemePushforwardHomSourceActionSection_base_smul f N W.unop r x
  exact originalSheafWithSourceAction_restrictIso_inv_apply H hres
    f.toRingCatSheafHom hbase (op U) h
end LinearStudy
