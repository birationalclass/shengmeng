module
public import Linear.AffineOriginalSourceActionSubopens
public import Linear.SourceRingSectionHom
public import Linear.SchemeModuleHomPostcomposeSection
public import Linear.SchemeModuleHomAffineOriginalSubopenExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 160000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : CommRingCat.{u}} (S : TopCat.Sheaf RingCat (Spec R))
variable (α : (Spec R).ringCatSheaf ⟶ S) (M N : SheafOfModules.{u} S)
variable [∀ W : (Spec R).Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (M.val.obj W)]
variable [∀ W : (Spec R).Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (N.val.obj W)]
variable [((SheafOfModules.restrictScalars α).obj M).IsQuasicoherent]
variable [((SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)).IsQuasicoherent]

/-- On an ACTUAL affine scheme, source linearity of the SAME original
base-module morphism on global sections implies source linearity for
EVERY local source function and EVERY local section on EVERY open.
The source module and source algebra are QC over the base. No target
QC, local compatibility certificate or surjective restriction is assumed. -/
theorem affineOriginalSourceLinear_on_every_open
    (C : (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M) ⟶
      (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj N))
    (htop : ∀ (b : S.obj.obj (op (⊤ : (Spec R).Opens)))
      (x : Γ((show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M),⊤)),
      C.app ⊤ (b • (show M.val.obj (op ⊤) from x)) =
        b • (show N.val.obj (op ⊤) from C.app ⊤ x))
    (W : (Spec R).Opens) (b : S.obj.obj (op W))
    (x : Γ((show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M),W)) :
    C.app W (b • (show M.val.obj (op W) from x)) =
      b • (show N.val.obj (op W) from C.app W x) := by
  let P : (Spec R).Modules := (SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)
  let A : (Spec R).Modules := (SheafOfModules.restrictScalars α).obj M
  let B : (Spec R).Modules := (SheafOfModules.restrictScalars α).obj N
  let h := schemeModuleHomPostcomposeSection P A B C W (sourceRingSectionHom S α M W x)
  let k := sourceRingSectionHom S α N W (C.app W x)
  have he : h = k := by
    apply schemeModuleHomAffineOriginalSubopen_evaluation_ext P B (𝟙 (Spec R))
      ⊤ (by simp) W le_top h k
    intro q
    dsimp only [h,k]
    rw [schemeModuleHomPostcomposeSection_evaluation,sourceRingSectionHom_evaluation,
      sourceRingSectionHom_evaluation]
    exact affineOriginalSourceAction_on_all_subopens S α M N C htop
      (show S.obj.obj (op ⊤) from q) W x
  have hev := congrArg (fun t => schemeModuleHomSectionEvaluation P B W t
    (show Γ(P,W) from b)) he
  dsimp only [h,k] at hev
  rw [schemeModuleHomPostcomposeSection_evaluation,sourceRingSectionHom_evaluation,
    sourceRingSectionHom_evaluation] at hev
  exact hev
end LinearStudy
