/- Copyright (c) 2022 Andrew Yang,2026 Joel Riou. Released under Apache 2.0. -/
module
public import Mathlib.CategoryTheory.Subfunctor.Sieves
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Types.Products
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
universe w v u
namespace CategoryTheory.Subfunctor
open Opposite
variable {C : Type u} [Category.{v} C]
/- Minimal inspected adaptation of Joel Riou mathlib4,commit04b574a2dc239b7964d235d5f66e31c37162b449. Apache2.0. Native objects retained;private continuation,NOT a completed Cech/native-H comparison. -/
/-- Given a family of objects `X : ι → C` in a category `C`, this is the subfunctor
of the constant functor `Cᵒᵖ ⥤ Type w` with value `PUnit` which sends an object
`U : C` to `Set.univ` when there exists a morphism `U ⟶ X i` for some `i`,
and `∅` otherwise. -/
def ofObjects {ι : Type*} (X : ι → C) :
    Subfunctor ((Functor.const Cᵒᵖ).obj PUnit.{w + 1}) where
  obj U := Set.ofPred (fun _ ↦ ∃ (i : ι), Nonempty (U.unop ⟶ X i))
  map := by
    rintro _ _ f _ ⟨i, ⟨g⟩⟩
    exact ⟨i, ⟨f.unop ≫ g⟩⟩

lemma ofObjects_obj_eq_univ {ι : Type*} {X : ι → C} {U : Cᵒᵖ} {i : ι} (f : U.unop ⟶ X i) :
    (ofObjects X).obj U = ⊤ := by
  ext
  simp only [ofObjects, Set.top_eq_univ, Set.mem_univ, iff_true]
  exact ⟨i, ⟨f⟩⟩

lemma ofObjects_obj_eq_empty {ι : Type*} {X : ι → C} {U : Cᵒᵖ}
    (h : ∀ (i : ι), IsEmpty (U.unop ⟶ X i)) :
    (ofObjects X).obj U = ∅ := by
  ext s
  change (∃ i, Nonempty (U.unop ⟶ X i)) ↔ False
  constructor
  · rintro ⟨i,⟨f⟩⟩
    letI : IsEmpty (U.unop ⟶ X i) := h i
    exact isEmptyElim f
  · intro hfalse
    exact hfalse.elim

/-- The value of `ofObjects X` on an object `U : Cᵒᵖ` contains a unique element
when there is a morphism `f : U.unop ⟶ X i`. -/
def uniqueOfObjectsObj {ι : Type*} {X : ι → C} {U : Cᵒᵖ} {i : ι} (f : U.unop ⟶ X i) :
    Unique ((ofObjects.{w} X).obj U) where
  default := ⟨.unit, by simp [ofObjects_obj_eq_univ f]⟩
  uniq := by rintro ⟨⟨⟩, _⟩; rfl

open Limits in
/-- `(ofObjects X).toFunctor` is a terminal object when there is a morphism
`f : T ⟶ X i` with `T` a terminal object. -/
noncomputable def isTerminalOfObjectsToFunctor {ι : Type*} (X : ι → C) {T : C} {i : ι} (f : T ⟶ X i)
    (hT : IsTerminal T) :
    IsTerminal (ofObjects X).toFunctor :=
  Functor.isTerminal
    (fun _ ↦ (Types.isTerminalEquivUnique _).2 (uniqueOfObjectsObj (hT.from _ ≫ f)))

end CategoryTheory.Subfunctor
