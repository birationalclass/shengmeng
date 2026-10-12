module
public import Linear.SchemePushforwardSourceModuleSheaf
public import Linear.PushforwardHomSourceScalarRecoveryInverse
public import Linear.SchemeAffineOriginalSourceLinearAllOpens
public import Linear.SchemePushforwardOriginalSourceAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 280000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}
variable (f : X ⟶ Y) (M : X.Modules) (N : Y.Modules)
variable (j : Spec R ⟶ Y) [IsOpenImmersion j]
attribute [local irreducible] schemeModuleHomModuleSheaf

/-- Recover the SAME original chart morphism as a base-module morphism
between the actual source-module sheaves. Scalar recovery is identity. -/
def schemePushforwardOriginalChartSourceBaseMorphism
    (C : (((Scheme.Modules.pushforward f).obj M).restrict j) ⟶
      ((schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N).restrict j)) :
    let A : Y.Modules := (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (schemePushforwardSourceModuleSheaf f M)
    let B : Y.Modules := (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
      (schemePushforwardHomSourceModuleSheaf f N)
    A.restrict j ⟶ B.restrict j :=
  (Scheme.Modules.restrictFunctor j).map
    (schemePushforwardSourceModuleSheaf_scalarRecoveryIso f M).hom ≫ C ≫
    (Scheme.Modules.restrictFunctor j).map
      (schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso f N).inv

theorem schemePushforwardOriginalChartSourceBaseMorphism_app
    (C : (((Scheme.Modules.pushforward f).obj M).restrict j) ⟶
      ((schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N).restrict j))
    (W : (Spec R).Opens)
    (x : Γ((show Y.Modules from
      (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
        (schemePushforwardSourceModuleSheaf f M)),j ''ᵁ W)) :
    (schemePushforwardOriginalChartSourceBaseMorphism f M N j C).app W x =
      (show Γ((show Y.Modules from
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).obj
          (schemePushforwardHomSourceModuleSheaf f N)),j ''ᵁ W)
        from C.app W (show Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ W) from x)) := by
  change (schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso f N).inv.val.app
      (op (j ''ᵁ W)) (C.app W x) = _
  exact schemePushforwardHomSourceModuleSheaf_scalarRecoveryIso_inv_apply
    f N (j ''ᵁ W) (C.app W x)

attribute [local irreducible] schemePushforwardOriginalChartSourceBaseMorphism

end LinearStudy
