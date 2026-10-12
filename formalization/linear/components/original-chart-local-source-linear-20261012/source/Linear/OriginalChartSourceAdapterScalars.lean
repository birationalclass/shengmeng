module
public import Linear.SchemePushforwardOriginalChartSourceAdapter
public import Linear.SchemePushforwardOriginalSourceAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 160000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}
attribute [local irreducible] schemeModuleHomModuleSheaf
  schemePushforwardOriginalChartSourceBaseMorphism

/-- Identity scalar recovery preserves the ORIGINAL local source-action
equation for the SAME chart morphism and EVERY actual local section. -/
theorem schemePushforwardOriginalChartSourceBaseMorphism_source_scalars_iff
    (f : X ⟶ Y) (M : X.Modules) (N : Y.Modules)
    (j : Spec R ⟶ Y) [IsOpenImmersion j]
    (C : (((Scheme.Modules.pushforward f).obj M).restrict j) ⟶
      ((schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N).restrict j))
    (W : (Spec R).Opens) (b : Γ(X,f ⁻¹ᵁ (j ''ᵁ W)))
    (x : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ W)) :
    let Cs := schemePushforwardOriginalChartSourceBaseMorphism f M N j C
    (Cs.app W
      ((show ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf).obj.obj (op (j ''ᵁ W)) from b) •
        (show (schemePushforwardSourceModuleSheaf f M).val.obj (op (j ''ᵁ W)) from x)) =
      (show ((TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf).obj.obj (op (j ''ᵁ W)) from b) •
        (show (schemePushforwardHomSourceModuleSheaf f N).val.obj (op (j ''ᵁ W)) from Cs.app W x)) ↔
    (C.app W (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ W) b x) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ W) b (C.app W x)) := by
  dsimp only
  rw [schemePushforwardOriginalChartSourceBaseMorphism_app,
    schemePushforwardOriginalChartSourceBaseMorphism_app]
  rfl
end LinearStudy
