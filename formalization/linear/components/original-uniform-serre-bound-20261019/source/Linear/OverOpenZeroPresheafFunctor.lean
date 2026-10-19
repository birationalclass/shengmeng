module
public import Linear.OverOpenZeroPresheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory Opposite DirectSum
universe u
variable {C : Type u} [Preorder C] (R : Cᵒᵖ ⥤ RingCat.{u}) (U : C)

/-- ACTUAL coefficient map on the extension-by-zero presheaves. -/
def overOpenZeroPresheafHom {M N : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)}
    (c : M ⟶ N) : overOpenZeroPresheaf R U M ⟶ overOpenZeroPresheaf R U N where
  app V := ModuleCat.ofHom (DirectSum.lmap (R := R.obj V) (fun i : V.unop ⟶ U => (c.app (op (Over.mk i))).hom))
  naturality {V W} f := by
    classical
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    change (DirectSum.lmap (R := R.obj W) (fun j : W.unop ⟶ U => (c.app (op (Over.mk j))).hom))
        (overOpenZeroMap R U M f (DirectSum.lof (R.obj V) _
          (fun j : V.unop ⟶ U => M.obj (op (Over.mk j))) i x)) =
      overOpenZeroMap R U N f
        ((DirectSum.lmap (R := R.obj V) (fun j : V.unop ⟶ U => (c.app (op (Over.mk j))).hom))
          (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => M.obj (op (Over.mk j))) i x))
    simp only [overOpenZeroMap_lof,DirectSum.lmap_lof]
    exact congrArg
      (DirectSum.lof (R.obj W) _ (fun j : W.unop ⟶ U => N.obj (op (Over.mk j))) (f.unop ≫ i))
      (PresheafOfModules.naturality_apply c
        (Over.homMk f.unop rfl : Over.mk (f.unop ≫ i) ⟶ Over.mk i).op x)

/-- Actual presheaf extension-by-zero functor,not an assumed adjoint. -/
def overOpenZeroPresheafFunctor :
    PresheafOfModules.{u} ((Over.forget U).op ⋙ R) ⥤ PresheafOfModules.{u} R where
  obj := overOpenZeroPresheaf R U
  map := overOpenZeroPresheafHom R U
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    exact DirectSum.lmap_id
  map_comp c d := by
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    exact DirectSum.lmap_comp _ _

/-- Prove mono preservation from ACTUAL pointwise direct-sum maps. -/
theorem overOpenZeroPresheafFunctor_preservesMonomorphisms :
    (overOpenZeroPresheafFunctor R U).PreservesMonomorphisms where
  preserves {M N} c hc := by
    classical
    letI := hc
    apply PresheafOfModules.mono_of_injective
    intro V
    exact (DirectSum.lmap_injective (R := R.obj V)
      (fun i : V.unop ⟶ U => (c.app (op (Over.mk i))).hom)).mpr
      (fun i => PresheafOfModules.injective_of_mono c (op (Over.mk i)))

end LinearStudy
