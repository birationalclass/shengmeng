module
public import Linear.SchemeModuleHomScalar
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

instance schemeModuleHomObjAddCommGroup (U : X.Opensᵒᵖ) :
    AddCommGroup ((schemeModuleHomPresheaf M N).obj U) :=
  schemeModuleHomAddCommGroup M N U.unop

instance schemeModuleHomObjModule (U : X.Opensᵒᵖ) :
    Module (X.presheaf.obj U) ((schemeModuleHomPresheaf M N).obj U) :=
  schemeModuleHomModule M N U.unop

/-- Original restrictions of local O-linear maps are semilinear for the
actual structure-sheaf restriction. -/
theorem schemeModuleHom_map_smul {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (r : Γ(X,U.unop)) (f : (schemeModuleHomPresheaf M N).obj U) :
    (schemeModuleHomPresheaf M N).map i (r • f) =
      X.presheaf.map i r • (schemeModuleHomPresheaf M N).map i f := by
  apply Subtype.ext
  change (_ : (Over.forget V.unop).op ⋙ M.presheaf ⟶
    (Over.forget V.unop).op ⋙ N.presheaf) = _
  ext W x
  change X.presheaf.map (W.unop.hom ≫ i.unop).op r •
      (show Γ(N,W.unop.left) from
        f.val.app ((Over.map i.unop).op.obj W) x) =
    X.presheaf.map W.unop.hom.op (X.presheaf.map i r) •
      (show Γ(N,W.unop.left) from
        f.val.app ((Over.map i.unop).op.obj W) x)
  congr 1
  exact congr($(X.presheaf.map_comp i W.unop.hom.op) r)

/-- The genuine local Hom abelian presheaf. The additive operations are
the original pointwise operations on local module morphisms. -/
def schemeModuleHomAbPresheaf : X.Opensᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of ((schemeModuleHomPresheaf M N).obj U)
  map i := AddCommGrpCat.ofHom {
    toFun := (schemeModuleHomPresheaf M N).map i
    map_zero' := by
      apply Subtype.ext
      change (_ : (Over.forget _).op ⋙ M.presheaf ⟶ (Over.forget _).op ⋙ N.presheaf) = _
      ext W x
      rfl
    map_add' f g := by
      apply Subtype.ext
      change (_ : (Over.forget _).op ⋙ M.presheaf ⟶ (Over.forget _).op ⋙ N.presheaf) = _
      ext W x
      rfl }
  map_id U := by
    ext f
    exact congr($((schemeModuleHomPresheaf M N).map_id U) f)
  map_comp i j := by
    ext f
    exact congr($((schemeModuleHomPresheaf M N).map_comp i j) f)

instance schemeModuleHomAbModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((schemeModuleHomAbPresheaf M N).obj U) :=
  schemeModuleHomObjModule M N U

/-- The local Hom presheaf with its proved ORIGINAL O-module structure. -/
def schemeModuleHomModulePresheaf : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj)
    (schemeModuleHomAbPresheaf M N) (fun {_ _} i r f => schemeModuleHom_map_smul M N i r f)

/-- The genuine internal Hom O-module SHEAF, whose original presheaf is
proved to be a sheaf. No sheafification or replacement of its sections is used. -/
def schemeModuleHomModuleSheaf : X.Modules where
  val := schemeModuleHomModulePresheaf M N
  isSheaf := by
    apply (Presheaf.isSheaf_iff_isSheaf_comp _ _ (forget Ab)).mpr
    exact schemeModuleHomPresheaf_isSheaf M N

end LinearStudy
