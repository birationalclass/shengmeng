module
public import Linear.SchemeModuleHomPresheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf
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

/-- The O-linear local maps form a subfunctor of the actual abelian Hom
presheaf. Its membership condition uses the original structure sheaf. -/
def schemeModuleHomSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := { f | schemeModuleHomOverLinear M N U.unop f }
  map i f hf := fun W r x => hf ((Over.map i.unop).op.obj W) r x

/-- O-linearity is local on the original scheme, since equality of target
sections is detected by restrictions to a covering sieve. This proves the
sheaf condition rather than changing the local Hom definition by sheafification. -/
theorem schemeModuleHomPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (schemeModuleHomPresheaf M N) := by
  let J := Opens.grothendieckTopology X
  let G := schemeModuleHomSubfunctor M N
  have hH : Presieve.IsSheaf J (presheafHom M.presheaf N.presheaf) := by
    have h := (N.isSheaf).hom M.presheaf
    rw [isSheaf_iff_isSheaf_of_type] at h
    exact h
  have hN : Presieve.IsSheaf J (N.presheaf ⋙ forget Ab) := by
    have h := Presheaf.isSheaf_comp_of_isSheaf J N.presheaf (forget Ab) N.isSheaf
    rw [isSheaf_iff_isSheaf_of_type] at h
    exact h
  have hG : Presieve.IsSheaf J G.toFunctor := by
    apply (G.isSheaf_iff hH).mpr
    intro U f hf W r x
    change ((Over.forget U.unop).op ⋙ M.presheaf ⟶
      (Over.forget U.unop).op ⋙ N.presheaf) at f
    have hcov := J.pullback_stable W.unop.hom hf
    apply (hN _ hcov).isSeparatedFor.ext
    intro Z i hi
    have hl := hi
    change schemeModuleHomOverLinear M N Z
      ((presheafHom M.presheaf N.presheaf).map (i ≫ W.unop.hom).op f) at hl
    have he := hl (op (Over.mk (𝟙 Z)))
      (X.presheaf.map i.op r) (M.presheaf.map i.op x)
    have heapp := presheafHom_map_app_op_mk_id
      (F := M.presheaf) (G := N.presheaf) (i ≫ W.unop.hom) f
    have he1 := congr($(heapp) (X.presheaf.map i.op r • M.presheaf.map i.op x))
    have he2 := congr($(heapp) (M.presheaf.map i.op x))
    have he' : f.app (op (Over.mk (i ≫ W.unop.hom)))
        (X.presheaf.map i.op r • M.presheaf.map i.op x) =
        X.presheaf.map i.op r • (show Γ(N, Z) from
          f.app (op (Over.mk (i ≫ W.unop.hom))) (M.presheaf.map i.op x)) :=
      he1.symm.trans (he.trans
        (congrArg (fun y : Γ(N, Z) => X.presheaf.map i.op r • y) he2))
    have hnat := f.naturality (Over.homMk i : Over.mk (i ≫ W.unop.hom) ⟶ W.unop).op
    have hnat1 := congr($(hnat) (r • x))
    have hnat2 := congr($(hnat) x)
    dsimp [presheafHom] at hnat1 hnat2
    rw [Scheme.Modules.map_smul] at hnat1
    change N.presheaf.map i.op (f.app W (r • x)) =
      N.presheaf.map i.op (r • (show Γ(N, W.unop.left) from f.app W x))
    change f.app (op (Over.mk (i ≫ W.unop.hom)))
      (X.presheaf.map i.op r • M.presheaf.map i.op x) =
      N.presheaf.map i.op (f.app W (r • x)) at hnat1
    change f.app (op (Over.mk (i ≫ W.unop.hom))) (M.presheaf.map i.op x) =
      N.presheaf.map i.op (f.app W x) at hnat2
    rw [← hnat1, Scheme.Modules.map_smul, ← hnat2]
    exact he'
  rw [isSheaf_iff_isSheaf_of_type]
  exact hG

/-- The actual sheaf of TYPES of local O-linear morphisms. Its local
sections were not replaced by sheafification; the original presheaf was
proved to satisfy the sheaf condition. The O-module action is a separate
construction, required before using an O-module internal Hom isomorphism. -/
def schemeModuleHomSheaf : TopCat.Sheaf (Type u) X where
  obj := schemeModuleHomPresheaf M N
  property := schemeModuleHomPresheaf_isSheaf M N

end LinearStudy
