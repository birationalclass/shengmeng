module
public import Linear.PushforwardHomSourceModuleSheaf
public import Linear.OriginalSheafSourceRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

/-- The actual source-ring Hom sheaf restricts to the ORIGINAL O_Y Hom
sheaf. The generic comparison already proves identity on all sections. -/
def schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso
    (f : X ⟶ Y) (N : Y.Modules) :
    (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (schemePushforwardHomSourceModuleSheaf f N) ≅
    schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N := by
  let H := schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
  let R := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
  letI (U : Y.Opensᵒᵖ) : Module (R.obj.obj U) (H.val.presheaf.obj U) :=
    schemePushforwardHomSourceModule f N U.unop
  have hres : ∀ ⦃U V : Y.Opensᵒᵖ⦄ (i : U ⟶ V) (b : R.obj.obj U)
      (h : H.val.presheaf.obj U),
      H.val.presheaf.map i (b • h) = R.obj.map i b • H.val.presheaf.map i h := by
    intro U V i b h
    exact schemePushforwardHomSourceActionSection_restrict f N i.unop b h
  have hbase : ∀ (U : Y.Opensᵒᵖ) (r : Y.ringCatSheaf.obj.obj U)
      (h : H.val.presheaf.obj U),
      (show R.obj.obj U from f.toRingCatSheafHom.hom.app U r) • h = r • h := by
    intro U r h
    exact schemePushforwardHomSourceActionSection_base_smul f N U.unop r h
  exact originalSheafWithSourceAction_restrictIso H hres f.toRingCatSheafHom hbase


/-- The scalar-recovery isomorphism is the identity on every ORIGINAL
section. Its compatibility with the original Hom is an actual theorem. -/
theorem schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso_hom_apply
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (h : Γ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (schemePushforwardHomSourceModuleSheaf f N),U)) :
    (schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso f N).hom.val.app (op U) h =
    (show Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U) from h) := rfl

end LinearStudy
