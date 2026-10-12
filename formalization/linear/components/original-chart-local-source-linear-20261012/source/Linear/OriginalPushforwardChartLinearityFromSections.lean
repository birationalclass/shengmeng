module
public import Linear.SchemePushforwardOriginalChartAllSourceScalars
public import Linear.SchemePushforwardSpecChartSectionAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 240000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}
variable (f : X ⟶ Y) (M : X.Modules) (N : Y.Modules)
variable (j : Spec R ⟶ Y) [IsOpenImmersion j]
variable (U : Y.Opens) (hi : j ''ᵁ ⊤ = U)
attribute [local irreducible] schemeModuleHomModuleSheaf

/-- Any original chart morphism agreeing with the SAME actual section
map inherits its source action. No extension constructor is unfolded. -/
theorem schemeOriginalPushforwardChartMorphism_top_source_scalars_from_sections
    (C : (((Scheme.Modules.pushforward f).obj M).restrict j) ⟶
      ((schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N).restrict j))
    (Φ : Γ((Scheme.Modules.pushforward f).obj M,U) →
      Γ(schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U))
    (hΦ : ∀ (b : Γ(X,f ⁻¹ᵁ U)) (t : Γ((Scheme.Modules.pushforward f).obj M,U)),
      Φ (schemePushforwardOriginalSourceActionSection f M U b t) =
        schemePushforwardHomSourceActionSection f N U b (Φ t))
    (hC : ∀ t : Γ((Scheme.Modules.pushforward f).obj M,U),
      C.app ⊤ (schemeModuleSpecChartSectionsEquiv ((Scheme.Modules.pushforward f).obj M) j U hi t) =
        schemeModuleSpecChartSectionsEquiv
          (schemeModuleHomModuleSheaf
            ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N)
          j U hi (Φ t))
    (b : Γ(X,f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens))))
    (t : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ ⊤)) :
    C.app ⊤ (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ ⊤) b t) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤) b (C.app ⊤ t) := by
  let F := (Scheme.Modules.pushforward f).obj M
  let H := schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
  let S := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
  let EF := schemeModuleSpecChartSectionsEquiv F j U hi
  let EH := schemeModuleSpecChartSectionsEquiv H j U hi
  obtain ⟨bU,hb⟩ := (ConcreteCategory.bijective_of_isIso
    (S.obj.mapIso (eqToIso hi).op).hom).2
      (show S.obj.obj (op (j ''ᵁ (⊤ : (Spec R).Opens))) from b)
  obtain ⟨tU,ht⟩ := EF.surjective t
  rw [← hb, ← ht]
  calc
    C.app ⊤ (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ ⊤)
      (S.obj.map (eqToIso hi).op.hom bU) (EF tU)) =
        C.app ⊤ (EF (schemePushforwardOriginalSourceActionSection f M U bU tU)) :=
      congrArg (fun z => C.app ⊤ z)
        (schemePushforwardSpecChartSectionsEquiv_original_source_smul f M j U hi bU tU).symm
    _ = EH (Φ (schemePushforwardOriginalSourceActionSection f M U bU tU)) := hC _
    _ = EH (schemePushforwardHomSourceActionSection f N U bU (Φ tU)) := congrArg EH (hΦ bU tU)
    _ = schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
        (S.obj.map (eqToIso hi).op.hom bU) (EH (Φ tU)) :=
      schemePushforwardHomSpecChartSectionsEquiv_original_source_smul f N j U hi bU (Φ tU)
    _ = schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
        (S.obj.map (eqToIso hi).op.hom bU) (C.app ⊤ (EF tU)) :=
      congrArg (fun z => schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
        (S.obj.map (eqToIso hi).op.hom bU) z) (hC tU).symm

variable [(((Scheme.Modules.pushforward f).obj M).restrict j).IsQuasicoherent]
variable [(((Scheme.Modules.pushforward f).obj
  (SheafOfModules.unit X.ringCatSheaf)).restrict j).IsQuasicoherent]

theorem schemeOriginalPushforwardChartMorphism_all_source_scalars_from_sections
    (C : (((Scheme.Modules.pushforward f).obj M).restrict j) ⟶
      ((schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N).restrict j))
    (Φ : Γ((Scheme.Modules.pushforward f).obj M,U) →
      Γ(schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U))
    (hΦ : ∀ (b : Γ(X,f ⁻¹ᵁ U)) (t : Γ((Scheme.Modules.pushforward f).obj M,U)),
      Φ (schemePushforwardOriginalSourceActionSection f M U b t) =
        schemePushforwardHomSourceActionSection f N U b (Φ t))
    (hC : ∀ t : Γ((Scheme.Modules.pushforward f).obj M,U),
      C.app ⊤ (schemeModuleSpecChartSectionsEquiv ((Scheme.Modules.pushforward f).obj M) j U hi t) =
        schemeModuleSpecChartSectionsEquiv
          (schemeModuleHomModuleSheaf
            ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N)
          j U hi (Φ t))
    (W : (Spec R).Opens) (b : Γ(X,f ⁻¹ᵁ (j ''ᵁ W)))
    (t : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ W)) :
    C.app W (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ W) b t) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ W) b (C.app W t) := by
  apply schemePushforwardOriginalChartMorphism_all_source_scalars f M N j
  intro b0 t0
  exact schemeOriginalPushforwardChartMorphism_top_source_scalars_from_sections
    f M N j U hi C Φ hΦ hC b0 t0
end LinearStudy
