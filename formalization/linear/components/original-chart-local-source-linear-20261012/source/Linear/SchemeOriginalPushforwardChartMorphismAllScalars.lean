module
public import Linear.SchemePushforwardOriginalChartAllSourceScalars
public import Linear.SchemePushforwardSpecChartSectionAction
public import Linear.SchemeModuleSpecChartMorphism
import all Linear.SchemeModuleSpecChartMorphism
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
variable (U : Y.Opens) (hi : j ''ᵁ ⊤ = U) (φ : R ⟶ Γ(Y,U))
variable (hφ : φ ≫ j.appLE U ⊤ (by rw [← hi]; exact (j.preimage_image_eq ⊤).ge) = (Scheme.ΓSpecIso R).inv)
variable [(((Scheme.Modules.pushforward f).obj M).restrict j).IsQuasicoherent]
attribute [local irreducible] schemeModuleHomModuleSheaf schemeModuleSpecChartMorphism

/-- The SAME original affine extension retains the ACTUAL whole-chart
source action after the original Spec section transports. -/
theorem schemeOriginalPushforwardChartMorphism_top_source_scalars
    (Φ : letI := Module.compHom Γ((Scheme.Modules.pushforward f).obj M,U) φ.hom
         let H := schemeModuleHomModuleSheaf
           ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
         letI := Module.compHom Γ(H,U) φ.hom
         Γ((Scheme.Modules.pushforward f).obj M,U) ≃ₗ[R] Γ(H,U))
    (hΦ : ∀ (b : Γ(X,f ⁻¹ᵁ U)) (t : Γ((Scheme.Modules.pushforward f).obj M,U)),
      Φ (schemePushforwardOriginalSourceActionSection f M U b t) =
        schemePushforwardHomSourceActionSection f N U b (Φ t))
    (b : Γ(X,f ⁻¹ᵁ (j ''ᵁ (⊤ : (Spec R).Opens))))
    (t : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ ⊤)) :
    let F := (Scheme.Modules.pushforward f).obj M
    let H := schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
    let C := schemeModuleSpecChartMorphism F H j U hi φ hφ Φ
    C.app ⊤ (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ ⊤) b t) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤) b (C.app ⊤ t) := by
  dsimp only
  let F := (Scheme.Modules.pushforward f).obj M
  let H := schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
  let S := (TopCat.Sheaf.pushforward RingCat f.base).obj X.ringCatSheaf
  letI := Module.compHom Γ(F,U) φ.hom
  letI := Module.compHom Γ(H,U) φ.hom
  let EF := schemeModuleSpecChartSectionsLinearEquiv F j U hi φ hφ
  let EH := schemeModuleSpecChartSectionsLinearEquiv H j U hi φ hφ
  let C := schemeModuleSpecChartMorphism F H j U hi φ hφ Φ
  have hc (x : Γ(F,U)) : C.app ⊤ (EF x) = EH (Φ x) :=
    schemeModuleSpecChartMorphism_sections F H j U hi φ hφ Φ x
  obtain ⟨bU,hb⟩ := (ConcreteCategory.bijective_of_isIso
    (S.obj.mapIso (eqToIso hi).op).hom).2
      (show S.obj.obj (op (j ''ᵁ (⊤ : (Spec R).Opens))) from b)
  obtain ⟨tU,ht⟩ := EF.surjective t
  rw [← hb, ← ht]
  calc
    C.app ⊤ (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ ⊤)
      (S.obj.map (eqToIso hi).op.hom bU) (EF tU)) =
        C.app ⊤ (EF (schemePushforwardOriginalSourceActionSection f M U bU tU)) := by
          exact congrArg (fun z => C.app ⊤ z)
            (schemePushforwardSpecChartSectionsEquiv_original_source_smul
              f M j U hi bU tU).symm
    _ = EH (Φ (schemePushforwardOriginalSourceActionSection f M U bU tU)) := hc _
    _ = EH (schemePushforwardHomSourceActionSection f N U bU (Φ tU)) := congrArg EH (hΦ bU tU)
    _ = schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
        (S.obj.map (eqToIso hi).op.hom bU) (EH (Φ tU)) :=
      schemePushforwardHomSpecChartSectionsEquiv_original_source_smul f N j U hi bU (Φ tU)
    _ = schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
        (S.obj.map (eqToIso hi).op.hom bU) (C.app ⊤ (EF tU)) := by
      exact congrArg (fun z => schemePushforwardHomSourceActionSection f N (j ''ᵁ ⊤)
        (S.obj.map (eqToIso hi).op.hom bU) z) (hc tU).symm

variable [(((Scheme.Modules.pushforward f).obj
  (SheafOfModules.unit X.ringCatSheaf)).restrict j).IsQuasicoherent]

/-- The SAME original extension is source linear on EVERY original chart
open. Local compatibility is derived from the actual whole-chart map;
there is no extra local certificate and no target-QC premise. -/
theorem schemeOriginalPushforwardChartMorphism_all_source_scalars
    (Φ : letI := Module.compHom Γ((Scheme.Modules.pushforward f).obj M,U) φ.hom
         let H := schemeModuleHomModuleSheaf
           ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
         letI := Module.compHom Γ(H,U) φ.hom
         Γ((Scheme.Modules.pushforward f).obj M,U) ≃ₗ[R] Γ(H,U))
    (hΦ : ∀ (b : Γ(X,f ⁻¹ᵁ U)) (t : Γ((Scheme.Modules.pushforward f).obj M,U)),
      Φ (schemePushforwardOriginalSourceActionSection f M U b t) =
        schemePushforwardHomSourceActionSection f N U b (Φ t))
    (W : (Spec R).Opens) (b : Γ(X,f ⁻¹ᵁ (j ''ᵁ W)))
    (t : Γ((Scheme.Modules.pushforward f).obj M,j ''ᵁ W)) :
    let F := (Scheme.Modules.pushforward f).obj M
    let H := schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
    let C := schemeModuleSpecChartMorphism F H j U hi φ hφ Φ
    C.app W (schemePushforwardOriginalSourceActionSection f M (j ''ᵁ W) b t) =
      schemePushforwardHomSourceActionSection f N (j ''ᵁ W) b (C.app W t) := by
  dsimp only
  apply schemePushforwardOriginalChartMorphism_all_source_scalars f M N j
  intro b0 t0
  exact schemeOriginalPushforwardChartMorphism_top_source_scalars f M N j U hi φ hφ Φ hΦ b0 t0
end LinearStudy
