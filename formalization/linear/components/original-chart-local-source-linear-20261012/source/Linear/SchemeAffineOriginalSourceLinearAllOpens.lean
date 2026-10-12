module
public import Linear.SourceRingModuleChartRestriction
public import Linear.AffineOriginalSourceLinearAllOpens
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 220000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {Y : Scheme.{u}} {R : CommRingCat.{u}}
variable (S : TopCat.Sheaf RingCat Y) (α : Y.ringCatSheaf ⟶ S)
variable (M N : SheafOfModules.{u} S) (j : Spec R ⟶ Y) [IsOpenImmersion j]
variable [∀ W : Y.Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (M.val.obj W)]
variable [∀ W : Y.Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (N.val.obj W)]
variable [((show Y.Modules from (SheafOfModules.restrictScalars α).obj M).restrict j).IsQuasicoherent]
variable [((show Y.Modules from (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)).restrict j).IsQuasicoherent]

/-- For the SAME actual base-module morphism on an ORIGINAL affine chart,
top-section source compatibility implies compatibility with EVERY actual
local source function on EVERY original chart open. Only the source module
and source algebra are QC; no local compatibility certificate is supplied. -/
theorem schemeAffineOriginalSourceLinear_on_every_open
    (C : ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M).restrict j) ⟶
      ((show Y.Modules from (SheafOfModules.restrictScalars α).obj N).restrict j))
    (htop : ∀ (b : S.obj.obj (op (j ''ᵁ (⊤ : (Spec R).Opens))))
      (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),j ''ᵁ ⊤)),
      C.app ⊤ (b • (show M.val.obj (op (j ''ᵁ ⊤)) from x)) =
        b • (show N.val.obj (op (j ''ᵁ ⊤)) from C.app ⊤ x))
    (W : (Spec R).Opens) (b : S.obj.obj (op (j ''ᵁ W)))
    (x : Γ((show Y.Modules from (SheafOfModules.restrictScalars α).obj M),j ''ᵁ W)) :
    C.app W (b • (show M.val.obj (op (j ''ᵁ W)) from x)) =
      b • (show N.val.obj (op (j ''ᵁ W)) from C.app W x) := by
  let Sj := schemeSourceRingChartRestriction S j
  let αj := schemeSourceRingChartRestrictionBaseMap S α j
  let Mj := schemeSourceModuleChartRestriction S j M
  let Nj := schemeSourceModuleChartRestriction S j N
  let eM := schemeSourceModuleChartRestriction_scalarRecoveryIso S α j M
  let eN := schemeSourceModuleChartRestriction_scalarRecoveryIso S α j N
  let eP := schemeSourceModuleChartRestriction_scalarRecoveryIso S α j (SheafOfModules.unit S)
  letI : ((SheafOfModules.restrictScalars αj).obj Mj).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso eM.symm inferInstance
  letI : ((SheafOfModules.restrictScalars αj).obj (SheafOfModules.unit Sj)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso eP.symm inferInstance
  letI (T : (Spec R).Opensᵒᵖ) : SMulCommClass (Sj.obj.obj T) (Sj.obj.obj T) (Mj.val.obj T) :=
    inferInstanceAs (SMulCommClass (S.obj.obj (op (j ''ᵁ T.unop)))
      (S.obj.obj (op (j ''ᵁ T.unop))) (M.val.obj (op (j ''ᵁ T.unop))))
  letI (T : (Spec R).Opensᵒᵖ) : SMulCommClass (Sj.obj.obj T) (Sj.obj.obj T) (Nj.val.obj T) :=
    inferInstanceAs (SMulCommClass (S.obj.obj (op (j ''ᵁ T.unop)))
      (S.obj.obj (op (j ''ᵁ T.unop))) (N.val.obj (op (j ''ᵁ T.unop))))
  let Cj : (show (Spec R).Modules from (SheafOfModules.restrictScalars αj).obj Mj) ⟶
      (show (Spec R).Modules from (SheafOfModules.restrictScalars αj).obj Nj) :=
    eM.hom ≫ C ≫ eN.inv
  have ht : ∀ (b : Sj.obj.obj (op (⊤ : (Spec R).Opens)))
      (t : Γ((show (Spec R).Modules from (SheafOfModules.restrictScalars αj).obj Mj),⊤)),
      Cj.app ⊤ (b • (show Mj.val.obj (op ⊤) from t)) =
        b • (show Nj.val.obj (op ⊤) from Cj.app ⊤ t) := by
    intro b t
    exact htop b t
  exact affineOriginalSourceLinear_on_every_open Sj αj Mj Nj Cj ht W b x
end LinearStudy
