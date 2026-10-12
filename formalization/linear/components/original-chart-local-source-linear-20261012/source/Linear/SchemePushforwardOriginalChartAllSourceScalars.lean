module
public import Linear.SchemePushforwardSourceModuleSheaf
public import Linear.OriginalChartSourceAdapterScalars
public import Linear.OriginalPushforwardSourceChartQuasicoherent
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
  schemePushforwardOriginalChartSourceBaseMorphism


variable [(((Scheme.Modules.pushforward f).obj M).restrict j).IsQuasicoherent]
variable [(((Scheme.Modules.pushforward f).obj
  (SheafOfModules.unit X.ringCatSheaf)).restrict j).IsQuasicoherent]

/-- On the ORIGINAL affine chart, compatibility of the SAME original
pushforward/Hom sheaf morphism with ALL whole-chart source functions
implies compatibility with EVERY source function on EVERY chart open.
The source sheaf and source algebra QC are retained; no target QC or
local source-compatibility certificate is assumed. -/
theorem schemePushforwardOriginalChartMorphism_all_source_scalars
    (C : (((Scheme.Modules.pushforward f).obj M).restrict j) ⟶
      ((schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N).restrict j))
    (htop : ∀ (b : Γ(X,f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens))))
      (x : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ ⊤)),
      C.app ⊤ (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ ⊤) b x) =
        schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤) b (C.app ⊤ x))
    (W : (Spec R).Opens) (b : Γ(X,f ⁻¹ᵁ (j ''ᵁ W)))
    (x : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ W)) :
    C.app W (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ W) b x) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ W) b (C.app W x) := by
  let S := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
  let α := f.toRingCatSheafHom
  let Ms := schemePushforwardSourceModuleSheaf f M
  let Ns := schemePushforwardHomSourceModuleSheaf f N
  letI : ((show Y.Modules from (SheafOfModules.restrictScalars α).obj Ms).restrict j).IsQuasicoherent :=
    schemePushforwardSourceModuleChart_isQuasicoherent f j M
  letI : ((show Y.Modules from (SheafOfModules.restrictScalars α).obj
      (SheafOfModules.unit S)).restrict j).IsQuasicoherent :=
    schemePushforwardSourceUnitChart_isQuasicoherent f j
  letI (T : Y.Opensᵒᵖ) : CommRing (S.obj.obj T) :=
    inferInstanceAs (CommRing Γ(X,f ⁻¹ᵁ T.unop))
  letI (T : Y.Opensᵒᵖ) : SMulCommClass (S.obj.obj T) (S.obj.obj T) (Ms.val.obj T) :=
    inferInstance
  letI (T : Y.Opensᵒᵖ) : SMulCommClass (S.obj.obj T) (S.obj.obj T) (Ns.val.obj T) :=
    inferInstance
  let Cs : ((show Y.Modules from (SheafOfModules.restrictScalars α).obj Ms).restrict j) ⟶
      ((show Y.Modules from (SheafOfModules.restrictScalars α).obj Ns).restrict j) :=
    schemePushforwardOriginalChartSourceBaseMorphism f M N j C
  have ht : ∀ (b : S.obj.obj (op (j ''ᵁ (⊤ : (Spec R).Opens))))
      (t : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj Ms),j ''ᵁ ⊤)),
      Cs.app ⊤ (b • (show Ms.val.obj (op (j ''ᵁ ⊤)) from t)) =
        b • (show Ns.val.obj (op (j ''ᵁ ⊤)) from Cs.app ⊤ t) := by
    intro b t
    exact (schemePushforwardOriginalChartSourceBaseMorphism_source_scalars_iff
      f M N j C ⊤ b t).2 (htop b t)
  have h := schemeAffineOriginalSourceLinear_on_every_open S α Ms Ns j Cs ht W b x
  exact (schemePushforwardOriginalChartSourceBaseMorphism_source_scalars_iff
    f M N j C W b x).1 h
end LinearStudy
