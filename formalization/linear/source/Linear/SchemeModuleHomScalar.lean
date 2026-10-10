module
public import Linear.SchemeModuleHomSheaf
public import Linear.SchemeModuleHomRestriction
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.Hom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules)

/-- Addition on the actual local O-linear Hom, transported from genuine
module-sheaf morphisms on the original open. -/
instance schemeModuleHomAddCommGroup (U : X.Opens) :
    AddCommGroup ((schemeModuleHomPresheaf M N).obj (op U)) :=
  (schemeModuleHomOverEquiv M N U).symm.addCommGroup

/-- Multiplication by an ORIGINAL structure-sheaf section acts on every
subopen by its actual ring restriction. -/
def schemeModuleHomScalar (U : X.Opens) (r : Γ(X,U))
    (f : (schemeModuleHomPresheaf M N).obj (op U)) :
    (schemeModuleHomPresheaf M N).obj (op U) := by
  let t : (presheafHom M.presheaf N.presheaf).obj (op U) := {
    app W := AddCommGrpCat.ofHom
      (X.presheaf.map W.unop.hom.op r •
        (show Γ(M,W.unop.left) →+ Γ(N,W.unop.left) from (f.val.app W).hom))
    naturality W Z i := by
      ext x
      have hf := congr($(f.val.naturality i) x)
      dsimp [presheafHom] at hf ⊢
      rw [Scheme.Modules.map_smul]
      rw [← hf]
      congr 1
      have he : X.presheaf.map W.unop.hom.op ≫
          X.presheaf.map i.unop.left.op = X.presheaf.map Z.unop.hom.op := by
        rw [← X.presheaf.map_comp, ← op_comp, i.unop.w]
      exact (congr($(he) r)).symm }
  refine ⟨t, ?_⟩
  intro W s x
  change X.presheaf.map W.unop.hom.op r •
      (show Γ(N,W.unop.left) from f.val.app W (s • x)) =
    s • (X.presheaf.map W.unop.hom.op r • (show Γ(N,W.unop.left) from f.val.app W x))
  rw [f.property W s x]
  exact smul_comm _ _ _

instance schemeModuleHomSMul (U : X.Opens) :
    SMul (Γ(X,U)) ((schemeModuleHomPresheaf M N).obj (op U)) :=
  ⟨schemeModuleHomScalar M N U⟩

@[simp] theorem schemeModuleHom_smul_app (U : X.Opens) (r : Γ(X,U))
    (f : (schemeModuleHomPresheaf M N).obj (op U))
    (W : (Over U)ᵒᵖ) (x : Γ(M,W.unop.left)) :
    (r • f).val.app W x = X.presheaf.map W.unop.hom.op r •
      (show Γ(N,W.unop.left) from f.val.app W x) := rfl

instance schemeModuleHomModule (U : X.Opens) :
    Module (Γ(X,U)) ((schemeModuleHomPresheaf M N).obj (op U)) where
  one_smul f := by
    apply Subtype.ext
    change (_ : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) = _
    ext W x
    change X.presheaf.map W.unop.hom.op 1 •
      (show Γ(N,W.unop.left) from f.val.app W x) = _
    rw [map_one, one_smul]
  mul_smul r s f := by
    apply Subtype.ext
    change (_ : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) = _
    ext W x
    change X.presheaf.map W.unop.hom.op (r * s) •
      (show Γ(N,W.unop.left) from f.val.app W x) =
      X.presheaf.map W.unop.hom.op r • (X.presheaf.map W.unop.hom.op s •
        (show Γ(N,W.unop.left) from f.val.app W x))
    rw [map_mul, mul_smul]
  smul_zero r := by
    apply Subtype.ext
    change (_ : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) = _
    ext W x
    change X.presheaf.map W.unop.hom.op r • (0 : Γ(N,W.unop.left)) = 0
    exact smul_zero _
  smul_add r f g := by
    apply Subtype.ext
    change (_ : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) = _
    ext W x
    change X.presheaf.map W.unop.hom.op r •
      ((show Γ(N,W.unop.left) from f.val.app W x) +
        (show Γ(N,W.unop.left) from g.val.app W x)) = _
    exact smul_add _ _ _
  add_smul r s f := by
    apply Subtype.ext
    change (_ : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) = _
    ext W x
    change X.presheaf.map W.unop.hom.op (r + s) •
      (show Γ(N,W.unop.left) from f.val.app W x) =
      X.presheaf.map W.unop.hom.op r • (show Γ(N,W.unop.left) from f.val.app W x) +
      X.presheaf.map W.unop.hom.op s • (show Γ(N,W.unop.left) from f.val.app W x)
    rw [map_add, add_smul]
  zero_smul f := by
    apply Subtype.ext
    change (_ : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) = _
    ext W x
    change X.presheaf.map W.unop.hom.op 0 •
      (show Γ(N,W.unop.left) from f.val.app W x) = 0
    rw [map_zero, zero_smul]

end LinearStudy
