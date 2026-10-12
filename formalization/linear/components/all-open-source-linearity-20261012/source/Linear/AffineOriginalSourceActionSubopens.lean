module
public import Linear.SourceGlobalSectionMultiplication
public import Linear.AffineQuasicoherentSourceMorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 120000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R : CommRingCat.{u}} (S : TopCat.Sheaf RingCat (Spec R))
variable (α : (Spec R).ringCatSheaf ⟶ S) (M N : SheafOfModules.{u} S)
variable [∀ W : (Spec R).Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (M.val.obj W)]
variable [∀ W : (Spec R).Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (N.val.obj W)]
variable [((SheafOfModules.restrictScalars α).obj M).IsQuasicoherent]

/-- Actual compatibility on the global sections of an affine scheme
forces compatibility with EVERY restricted global source scalar on
EVERY section over EVERY subopen. Source QC gives faithful global
sections; no target QC or surjectivity of restrictions is assumed. -/
theorem affineOriginalSourceAction_on_all_subopens
    (C : (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M) ⟶
      (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj N))
    (htop : ∀ (b : S.obj.obj (op (⊤ : (Spec R).Opens)))
      (x : Γ((show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M),⊤)),
      C.app ⊤ (b • (show M.val.obj (op ⊤) from x)) =
        b • (show N.val.obj (op ⊤) from C.app ⊤ x))
    (b : S.obj.obj (op (⊤ : (Spec R).Opens))) (W : (Spec R).Opens)
    (x : Γ((show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M),W)) :
    C.app W (S.obj.map W.leTop.op b • (show M.val.obj (op W) from x)) =
      S.obj.map W.leTop.op b • (show N.val.obj (op W) from C.app W x) := by
  let A : (Spec R).Modules := (SheafOfModules.restrictScalars α).obj M
  let B : (Spec R).Modules := (SheafOfModules.restrictScalars α).obj N
  have he : sourceGlobalSectionMultiplication S α M b ≫ C =
      C ≫ sourceGlobalSectionMultiplication S α N b := by
    apply (affineQuasicoherentSourceMorphismsEquiv A B).injective
    rw [affineQuasicoherentSourceMorphismsEquiv_apply,
      affineQuasicoherentSourceMorphismsEquiv_apply]
    apply ModuleCat.hom_ext
    ext t
    change C.app ⊤ (S.obj.map (𝟙 (op (⊤ : (Spec R).Opens))) b •
        (show M.val.obj (op ⊤) from t)) =
      S.obj.map (𝟙 (op (⊤ : (Spec R).Opens))) b •
        (show N.val.obj (op ⊤) from C.app ⊤ t)
    rw [S.obj.map_id]
    exact htop b t
  exact congrArg (fun f => f.app W x) he
end LinearStudy
