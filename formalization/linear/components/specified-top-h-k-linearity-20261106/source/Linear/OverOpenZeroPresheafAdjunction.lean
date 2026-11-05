module
public import Linear.OverOpenZeroPresheafFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory Opposite DirectSum
universe u
variable {C : Type u} [Preorder C] (R : Cᵒᵖ ⥤ RingCat.{u}) (U : C)
variable (N : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)) (M : PresheafOfModules.{u} R)

/-- Restrict an ACTUAL map out of extension by zero to original summands. -/
def overOpenZeroHomRestrict (a : overOpenZeroPresheaf R U N ⟶ M) :
    N ⟶ (PresheafOfModules.pushforward₀ (Over.forget U) R).obj M where
  app A := ModuleCat.ofHom ((a.app (op A.unop.left)).hom.comp
    (DirectSum.lof (R.obj (op A.unop.left)) _
      (fun i : A.unop.left ⟶ U => N.obj (op (Over.mk i))) A.unop.hom))
  naturality {A B} f := by
    classical
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := PresheafOfModules.naturality_apply a f.unop.left.op
      (DirectSum.lof (R.obj (op A.unop.left)) _
        (fun i : A.unop.left ⟶ U => N.obj (op (Over.mk i))) A.unop.hom x)
    change a.app (op B.unop.left)
        (overOpenZeroMap R U N f.unop.left.op
          (DirectSum.lof (R.obj (op A.unop.left)) _
            (fun i : A.unop.left ⟶ U => N.obj (op (Over.mk i))) A.unop.hom x)) = _ at h
    rw [overOpenZeroMap_lof] at h
    change a.app (op B.unop.left)
        (DirectSum.lof (R.obj (op B.unop.left)) _
          (fun i : B.unop.left ⟶ U => N.obj (op (Over.mk i))) B.unop.hom (N.map f x)) =
      M.map f.unop.left.op (a.app (op A.unop.left)
        (DirectSum.lof (R.obj (op A.unop.left)) _
          (fun i : A.unop.left ⟶ U => N.obj (op (Over.mk i))) A.unop.hom x))
    exact h

/-- Extend an ACTUAL local map using the direct-sum universal property. -/
def overOpenZeroHomExtend
    (c : N ⟶ (PresheafOfModules.pushforward₀ (Over.forget U) R).obj M) :
    overOpenZeroPresheaf R U N ⟶ M where
  app V := ModuleCat.ofHom (DirectSum.toModule (R.obj V) _ (M.obj V)
    (fun i : V.unop ⟶ U => (c.app (op (Over.mk i))).hom))
  naturality {V W} f := by
    classical
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change (DirectSum.toModule (R.obj W) _ (M.obj W)
        (fun j : W.unop ⟶ U => (c.app (op (Over.mk j))).hom))
        (overOpenZeroMap R U N f (DirectSum.lof (R.obj V) _
          (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x)) =
      M.map f ((DirectSum.toModule (R.obj V) _ (M.obj V)
        (fun j : V.unop ⟶ U => (c.app (op (Over.mk j))).hom))
          (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x))
    rw [overOpenZeroMap_lof,DirectSum.toModule_lof,DirectSum.toModule_lof]
    exact PresheafOfModules.naturality_apply c
      (Over.homMk f.unop rfl : Over.mk (f.unop ≫ i) ⟶ Over.mk i).op x

/-- Evaluate the SAME extension on an actual original summand. -/
theorem overOpenZeroHomExtend_lof
    (c : N ⟶ (PresheafOfModules.pushforward₀ (Over.forget U) R).obj M)
    (V : Cᵒᵖ) (i : V.unop ⟶ U) (x : N.obj (op (Over.mk i))) :
    (overOpenZeroHomExtend R U N M c).app V
        (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x) =
      c.app (op (Over.mk i)) x := by
  classical
  change (DirectSum.toModule (R.obj V) _ (M.obj V)
    (fun j : V.unop ⟶ U => (c.app (op (Over.mk j))).hom))
      (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x) = _
  rw [DirectSum.toModule_lof]
  rfl

/-- PROVED actual Hom equivalence;no desired adjunction is supplied. -/
def overOpenZeroHomEquiv :
    (overOpenZeroPresheaf R U N ⟶ M) ≃
      (N ⟶ (PresheafOfModules.pushforward₀ (Over.forget U) R).obj M) where
  toFun := overOpenZeroHomRestrict R U N M
  invFun := overOpenZeroHomExtend R U N M
  left_inv a := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change (overOpenZeroHomExtend R U N M _).app V
      (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x) = _
    rw [overOpenZeroHomExtend_lof]
    rfl
  right_inv c := by
    apply PresheafOfModules.hom_ext
    intro A
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (overOpenZeroHomExtend R U N M c).app (op A.unop.left)
      (DirectSum.lof (R.obj (op A.unop.left)) _
        (fun i : A.unop.left ⟶ U => N.obj (op (Over.mk i))) A.unop.hom x) = _
    rw [overOpenZeroHomExtend_lof]
    rfl

/-- Actual presheaf extension-by-zero/restriction adjunction. -/
def overOpenZeroPresheafAdjunction :
    overOpenZeroPresheafFunctor R U ⊣ PresheafOfModules.pushforward₀ (Over.forget U) R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := overOpenZeroHomEquiv R U
    homEquiv_naturality_left_symm := by
      intro N' N M c a
      apply PresheafOfModules.hom_ext
      intro V
      apply ModuleCat.hom_ext
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      change (overOpenZeroHomExtend R U N' M _).app V
          (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N'.obj (op (Over.mk j))) i x) =
        (overOpenZeroHomExtend R U N M a).app V
          ((DirectSum.lmap (R := R.obj V) (fun j : V.unop ⟶ U => (c.app (op (Over.mk j))).hom))
            (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N'.obj (op (Over.mk j))) i x))
      rw [overOpenZeroHomExtend_lof,DirectSum.lmap_lof,overOpenZeroHomExtend_lof]
      rfl
    homEquiv_naturality_right := by
      intros
      apply PresheafOfModules.hom_ext
      intro A
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl }

end LinearStudy
