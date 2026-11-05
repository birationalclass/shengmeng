module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Over.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory Opposite DirectSum
universe u
variable {C : Type u} [Preorder C] (R : Cᵒᵖ ⥤ RingCat.{u}) (U : C)
  (N : PresheafOfModules.{u} ((Over.forget U).op ⋙ R))

/-- Actual extension-by-zero presheaf object via a direct sum over the
actual arrows V->U. For opens,there is at most one summand. -/
def overOpenZeroObj (V : Cᵒᵖ) : ModuleCat.{u} (R.obj V) :=
  ModuleCat.of (R.obj V) (⨁ (i : V.unop ⟶ U), N.obj (op (Over.mk i)))

def overOpenZeroMap {V W : Cᵒᵖ} (f : V ⟶ W) :
    overOpenZeroObj R U N V ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj (overOpenZeroObj R U N W) := by
  classical
  letI : Module (R.obj V) (overOpenZeroObj R U N W) :=
    ((ModuleCat.restrictScalars (R.map f).hom).obj (overOpenZeroObj R U N W)).isModule
  exact ModuleCat.ofHom (DirectSum.toModule (R.obj V) _ _ (fun i =>
    (((ModuleCat.restrictScalars (R.map f).hom).map
      (ModuleCat.ofHom (DirectSum.lof (R.obj W) _
        (fun j : W.unop ⟶ U => N.obj (op (Over.mk j))) (f.unop ≫ i)))).hom).comp
      (N.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ i) ⟶ Over.mk i).op).hom))

/-- Actual restriction of an original summand,with no dependent-if casts. -/
theorem overOpenZeroMap_lof {V W : Cᵒᵖ} (f : V ⟶ W) (i : V.unop ⟶ U)
    (x : N.obj (op (Over.mk i))) :
    overOpenZeroMap R U N f
        (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x) =
      DirectSum.lof (R.obj W) _ (fun j : W.unop ⟶ U => N.obj (op (Over.mk j))) (f.unop ≫ i)
        (N.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ i) ⟶ Over.mk i).op x) := by
  classical
  letI : Module (R.obj V) (overOpenZeroObj R U N W) :=
    ((ModuleCat.restrictScalars (R.map f).hom).obj (overOpenZeroObj R U N W)).isModule
  exact DirectSum.toModule_lof (R := R.obj V)
    (φ := fun j =>
      (((ModuleCat.restrictScalars (R.map f).hom).map
        (ModuleCat.ofHom (DirectSum.lof (R.obj W) _
          (fun k : W.unop ⟶ U => N.obj (op (Over.mk k))) (f.unop ≫ j)))).hom).comp
        (N.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ j) ⟶ Over.mk j).op).hom) i x

theorem overOpenZeroMap_id (V : Cᵒᵖ) :
    overOpenZeroMap R U N (𝟙 V) =
      (ModuleCat.restrictScalarsId' (R.map (𝟙 V)).hom
        (congrArg RingCat.Hom.hom (R.map_id V))).inv.app (overOpenZeroObj R U N V) := by
  classical
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  change overOpenZeroMap R U N (𝟙 V)
      (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x) = _
  change overOpenZeroMap R U N (𝟙 V)
      (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x) =
    DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x
  rw [overOpenZeroMap_lof]
  change DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i
    (N.map (𝟙 (op (Over.mk i))) x) = _
  rw [N.map_id]
  rfl

theorem overOpenZeroMap_comp {V W Z : Cᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) :
    overOpenZeroMap R U N (f ≫ g) =
      overOpenZeroMap R U N f ≫
        (ModuleCat.restrictScalars (R.map f).hom).map (overOpenZeroMap R U N g) ≫
          (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
            (congrArg RingCat.Hom.hom (R.map_comp f g))).inv.app (overOpenZeroObj R U N Z) := by
  classical
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  change overOpenZeroMap R U N (f ≫ g)
      (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x) =
    overOpenZeroMap R U N g (overOpenZeroMap R U N f
      (DirectSum.lof (R.obj V) _ (fun j : V.unop ⟶ U => N.obj (op (Over.mk j))) i x))
  simp only [overOpenZeroMap_lof]
  exact congrArg
    (DirectSum.lof (R.obj Z) _ (fun j : Z.unop ⟶ U => N.obj (op (Over.mk j))) (g.unop ≫ (f.unop ≫ i)))
    (N.map_comp_apply
      (Over.homMk f.unop rfl : Over.mk (f.unop ≫ i) ⟶ Over.mk i).op
      (Over.homMk g.unop rfl : Over.mk (g.unop ≫ (f.unop ≫ i)) ⟶ Over.mk (f.unop ≫ i)).op x)

/-- Actual presheaf extension by zero,BEFORE sheafification. -/
def overOpenZeroPresheaf : PresheafOfModules.{u} R where
  obj := overOpenZeroObj R U N
  map := overOpenZeroMap R U N
  map_id := overOpenZeroMap_id R U N
  map_comp := overOpenZeroMap_comp R U N

end LinearStudy
