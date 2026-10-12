module
public import Linear.OriginalBaseMorphismSourceLift
public import Linear.AffineOriginalSourceLinearAllOpens
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 160000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : CommRingCat.{u}} (S : TopCat.Sheaf RingCat (Spec R))
variable (α : (Spec R).ringCatSheaf ⟶ S) (M N : SheafOfModules.{u} S)
variable [∀ W : (Spec R).Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (M.val.obj W)]
variable [∀ W : (Spec R).Opensᵒᵖ, SMulCommClass (S.obj.obj W) (S.obj.obj W) (N.val.obj W)]
variable [((SheafOfModules.restrictScalars α).obj M).IsQuasicoherent]
variable [((SheafOfModules.restrictScalars α).obj (SheafOfModules.unit S)).IsQuasicoherent]

/-- The SAME affine base-module sheaf morphism lifts to an ACTUAL
source-module sheaf morphism. All local compatibility is DERIVED from
the global-section source relation and affine QC, rather than supplied. -/
def affineOriginalSourceMorphismLift
    (C : (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M) ⟶
      (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj N))
    (htop : ∀ (b : S.obj.obj (op (⊤ : (Spec R).Opens)))
      (x : Γ((show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M),⊤)),
      C.app ⊤ (b • (show M.val.obj (op ⊤) from x)) =
        b • (show N.val.obj (op ⊤) from C.app ⊤ x)) : M ⟶ N :=
  originalBaseMorphismSourceLift S α M N C (fun W b x =>
    affineOriginalSourceLinear_on_every_open S α M N C htop W b x)

theorem affineOriginalSourceMorphismLift_scalar_recovery
    (C : (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M) ⟶
      (show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj N))
    (htop : ∀ (b : S.obj.obj (op (⊤ : (Spec R).Opens)))
      (x : Γ((show (Spec R).Modules from (SheafOfModules.restrictScalars α).obj M),⊤)),
      C.app ⊤ (b • (show M.val.obj (op ⊤) from x)) =
        b • (show N.val.obj (op ⊤) from C.app ⊤ x)) :
    (SheafOfModules.restrictScalars α).map
      (affineOriginalSourceMorphismLift S α M N C htop) = C :=
  originalBaseMorphismSourceLift_scalar_recovery S α M N C _
end LinearStudy
