module
public import Linear.SourceModuleSpecChartSectionAction
public import Linear.SchemePushforwardSourceModuleSheaf
public import Linear.PushforwardHomSourceScalarRecovery
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
variable (f : X ⟶ Y) (M : X.Modules) (N : Y.Modules)
variable (j : Spec R ⟶ Y) [IsOpenImmersion j]
attribute [local irreducible] schemeModuleHomModuleSheaf

theorem schemePushforwardSpecChartSectionsEquiv_original_source_smul
    (U : Y.Opens) (hi : j ''ᵁ ⊤ = U) (b : Γ(X,f ⁻¹ᵁ U))
    (x : Γ((Scheme.Modules.pushforward f).obj M,U)) :
    let S := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
    schemeModuleSpecChartSectionsEquiv ((Scheme.Modules.pushforward f).obj M) j U hi
      (schemePushforwardOriginalSourceActionSection f M U b x) =
    schemePushforwardOriginalSourceActionSection f M (j ''ᵁ ⊤)
      (show Γ(X,f ⁻¹ᵁ (j ''ᵁ ⊤)) from S.obj.map (eqToIso hi).op.hom b)
      (schemeModuleSpecChartSectionsEquiv ((Scheme.Modules.pushforward f).obj M) j U hi x) := by
  dsimp only
  let i := (eqToIso hi).op.hom
  change M.val.presheaf.map ((Opens.map f.base).op.map i)
      (b • (show Γ(M,f ⁻¹ᵁ U) from x)) =
    X.ringCatSheaf.obj.map ((Opens.map f.base).op.map i) b •
      M.val.presheaf.map ((Opens.map f.base).op.map i) x
  exact M.val.map_smul ((Opens.map f.base).op.map i) b x

theorem schemePushforwardHomSpecChartSectionsEquiv_original_source_smul
    (U : Y.Opens) (hi : j ''ᵁ ⊤ = U) (b : Γ(X,f ⁻¹ᵁ U))
    (x : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    let S := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
    let H := schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
    schemeModuleSpecChartSectionsEquiv H j U hi
      (schemePushforwardHomSourceActionSection f N U b x) =
    schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
      (show Γ(X,f ⁻¹ᵁ (j ''ᵁ ⊤)) from S.obj.map (eqToIso hi).op.hom b)
      (schemeModuleSpecChartSectionsEquiv H j U hi x) := by
  dsimp only
  let H := schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
  change H.presheaf.map (eqToIso hi).op.hom
      (schemePushforwardHomSourceActionSection f N U b x) =
    schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
      (X.presheaf.map ((Opens.map f.base).map (eqToIso hi).hom).op b)
      (H.presheaf.map (eqToIso hi).op.hom x)
  exact schemePushforwardHomSourceActionSection_restrict f N (eqToIso hi).hom b x

end LinearStudy
