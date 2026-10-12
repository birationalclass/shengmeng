module
public import Linear.SchemeAffineOriginalSourceLinearAllOpens
public import Linear.SourceModuleSpecChartSectionAction
public import Linear.SchemeModuleSpecChartMorphism
import all Linear.SchemeModuleSpecChartMorphism
public import Linear.SchemeModuleSpecChartSectionsLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 250000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {Y : Scheme.{u}} {R : CommRingCat.{u}}
variable (S : TopCat.Sheaf RingCat Y) (α : Y.ringCatSheaf ⟶ S)
variable (M N : SheafOfModules.{u} S) (j : Spec R ⟶ Y) [IsOpenImmersion j]
variable [∀ W : Y.Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (M.val.obj W)]
variable [∀ W : Y.Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (N.val.obj W)]
variable [((show Y.Modules from (SheafOfModules.restrictScalars α).obj M).restrict j).IsQuasicoherent]
variable [((show Y.Modules from (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)).restrict j).IsQuasicoherent]

/-- The SAME original affine-QC extension of an actual chart-section
comparison preserves every local source scalar on every chart open.
Only top-section compatibility is an input here; applications must derive
it from the original comparison, rather than assume a sheaf certificate. -/
theorem sourceModuleSpecChartMorphism_all_source_smul
    (U : Y.Opens) (hi : j ''ᵁ ⊤ = U) (φ : R ⟶ Γ(Y,U))
    (hφ : φ ≫ j.appLE U ⊤ (by rw [← hi]; exact (j.preimage_image_eq ⊤).ge) =
      (Scheme.ΓSpecIso R).inv)
    (Φ : let A : Y.Modules := (SheafOfModules.restrictScalars α).obj M
         let B : Y.Modules := (SheafOfModules.restrictScalars α).obj N
         letI := Module.compHom Γ(A,U) φ.hom
         letI := Module.compHom Γ(B,U) φ.hom
         Γ(A,U) ≃ₗ[R] Γ(B,U))
    (htop : ∀ (b : S.obj.obj (op U))
      (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),U)),
      Φ (b • (show M.val.obj (op U) from x)) =
        b • (show N.val.obj (op U) from Φ x))
    (W : (Spec R).Opens) (b : S.obj.obj (op (j ''ᵁ W)))
    (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),j ''ᵁ W)) :
    let A : Y.Modules := (SheafOfModules.restrictScalars α).obj M
    let B : Y.Modules := (SheafOfModules.restrictScalars α).obj N
    let C := schemeModuleSpecChartMorphism A B j U hi φ hφ Φ
    C.app W (b • (show M.val.obj (op (j ''ᵁ W)) from x)) =
      b • (show N.val.obj (op (j ''ᵁ W)) from C.app W x) := by
  let A : Y.Modules := (SheafOfModules.restrictScalars α).obj M
  let B : Y.Modules := (SheafOfModules.restrictScalars α).obj N
  letI := Module.compHom Γ(A,U) φ.hom
  letI := Module.compHom Γ(B,U) φ.hom
  let EA := schemeModuleSpecChartSectionsLinearEquiv A j U hi φ hφ
  let EB := schemeModuleSpecChartSectionsLinearEquiv B j U hi φ hφ
  let C := schemeModuleSpecChartMorphism A B j U hi φ hφ Φ
  have hc (t : Γ(A,U)) : C.app ⊤ (EA t) = EB (Φ t) :=
    schemeModuleSpecChartMorphism_sections A B j U hi φ hφ Φ t
  have ht : ∀ (c : S.obj.obj (op (j ''ᵁ (⊤ : (Spec R).Opens))))
      (t : Γ(A,j ''ᵁ ⊤)),
      C.app ⊤ (c • (show M.val.obj (op (j ''ᵁ ⊤)) from t)) =
        c • (show N.val.obj (op (j ''ᵁ ⊤)) from C.app ⊤ t) := by
    intro c t
    obtain ⟨a,ha⟩ := (ConcreteCategory.bijective_of_isIso
      (S.obj.mapIso (eqToIso hi).op).hom).2 c
    obtain ⟨v,hv⟩ := EA.surjective t
    rw [← ha,← hv]
    calc
      C.app ⊤ (S.obj.map (eqToIso hi).op.hom a •
          (show M.val.obj (op (j ''ᵁ ⊤)) from EA v)) =
        C.app ⊤ (EA (a • (show M.val.obj (op U) from v))) := by
          exact congrArg (fun z => C.app ⊤ z)
            (sourceModuleSpecChartSectionsEquiv_smul S α M j U hi a v).symm
      _ = EB (Φ (a • (show M.val.obj (op U) from v))) := hc _
      _ = EB (a • (show N.val.obj (op U) from Φ v)) := congrArg EB (htop a v)
      _ = S.obj.map (eqToIso hi).op.hom a •
        (show N.val.obj (op (j ''ᵁ ⊤)) from EB (Φ v)) :=
          sourceModuleSpecChartSectionsEquiv_smul S α N j U hi a (Φ v)
      _ = S.obj.map (eqToIso hi).op.hom a •
        (show N.val.obj (op (j ''ᵁ ⊤)) from C.app ⊤ (EA v)) :=
          congrArg (fun z => S.obj.map (eqToIso hi).op.hom a •
            (show N.val.obj (op (j ''ᵁ ⊤)) from z)) (hc v).symm
  dsimp only
  exact schemeAffineOriginalSourceLinear_on_every_open S α M N j C ht W b x
end LinearStudy
