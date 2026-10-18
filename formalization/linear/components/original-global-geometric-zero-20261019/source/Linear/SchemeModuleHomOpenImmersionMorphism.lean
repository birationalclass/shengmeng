module
public import Linear.SchemeModuleHomOpenImmersionRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}} (M N : X.Modules)
variable (j : Y ⟶ X) [IsOpenImmersion j]

/-- The genuine internal Hom comparison under the original open
immersion. Its map on every subopen is the actual restriction of local
O-linear maps, with no assumed Hom-sheaf compatibility. -/
def schemeModuleHomOpenImmersionMorphism :
    (schemeModuleHomModuleSheaf M N).restrict j ⟶
      schemeModuleHomModuleSheaf (M.restrict j) (N.restrict j) := ⟨{
  app W := by
    let T := (schemeModuleHomModuleSheaf M N).restrict j
    let L := schemeModuleHomModuleSheaf (M.restrict j) (N.restrict j)
    letI := (T.val.obj W).isModule
    let f : (T.val.obj W) →ₗ[Y.ringCatSheaf.obj.obj W] (L.val.obj W) := {
    toFun := schemeModuleHomOpenImmersionRestrictSection M N j W.unop
    map_add' f g := by
      apply Subtype.ext
      change (_ : (Over.forget W.unop).op ⋙ (M.restrict j).presheaf ⟶
        (Over.forget W.unop).op ⋙ (N.restrict j).presheaf) = _
      ext Z x
      rfl
    map_smul' r f := by
      apply Subtype.ext
      change (_ : (Over.forget W.unop).op ⋙ (M.restrict j).presheaf ⟶
        (Over.forget W.unop).op ⋙ (N.restrict j).presheaf) = _
      ext Z x
      change X.presheaf.map (j.opensFunctor.map Z.unop.hom).op
          ((j.appIso W.unop).inv r) •
          (show Γ(N,j ''ᵁ Z.unop.left) from
            f.val.app ((Over.post (X := W.unop) j.opensFunctor).op.obj Z) x) =
        (j.appIso Z.unop.left).inv (Y.presheaf.map Z.unop.hom.op r) •
          (show Γ(N,j ''ᵁ Z.unop.left) from
            f.val.app ((Over.post (X := W.unop) j.opensFunctor).op.obj Z) x)
      congr 1
      exact (congr($(j.appIso_inv_naturality Z.unop.hom.op) r)).symm }
    exact (ModuleCat.homEquiv (M := T.val.obj W) (N := L.val.obj W)).symm f
  naturality i := by
    ext f
    apply Subtype.ext
    change (_ : (Over.forget _).op ⋙ (M.restrict j).presheaf ⟶
      (Over.forget _).op ⋙ (N.restrict j).presheaf) = _
    ext Z x
    rfl }⟩
end LinearStudy
