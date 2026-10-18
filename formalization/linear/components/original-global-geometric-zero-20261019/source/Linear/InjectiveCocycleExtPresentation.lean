module
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
variable {N : A} (I : InjectiveResolution N) (P : A) (q : ℕ)

/-- Actual degree-q cocycles in the SAME coefficient injective resolution. -/
def injectiveCocycleGroup : AddSubgroup (P ⟶ I.cocomplex.X q) where
  carrier := {f | f ≫ I.cocomplex.d q (q+1) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change f ≫ I.cocomplex.d q (q+1) = 0 at hf
    change g ≫ I.cocomplex.d q (q+1) = 0 at hg
    change (f+g) ≫ I.cocomplex.d q (q+1) = 0
    rw [Preadditive.add_comp,hf,hg,add_zero]
  neg_mem' := by
    intro f hf
    change f ≫ I.cocomplex.d q (q+1) = 0 at hf
    change (-f) ≫ I.cocomplex.d q (q+1) = 0
    rw [Preadditive.neg_comp,hf,neg_zero]

/-- The native ACTUAL Ext class of the SAME cocycle,as an additive map. -/
def injectiveCocycleExtMap : injectiveCocycleGroup I P q →+ Ext P N q where
  toFun f := I.extMk f.val (q+1) rfl f.property
  map_zero' := I.extMk_zero _ _
  map_add' f g := (I.add_extMk f.val g.val (q+1) rfl f.property g.property).symm

theorem injectiveCocycleExtMap_surjective :
    Function.Surjective (injectiveCocycleExtMap I P q) := by
  intro e
  obtain ⟨f,hf,he⟩ := I.extMk_surjective e (q+1) rfl
  exact ⟨⟨f,hf⟩,he⟩

/-- In positive degree,the kernel consists EXACTLY of actual boundaries
in the SAME injective resolution. Reuse native Ext presentation,not a
surjectivity or desired kernel condition supplied as a premise. -/
theorem injectiveCocycleExtMap_succ_eq_zero_iff (n : ℕ)
    (f : injectiveCocycleGroup I P (n+1)) :
    injectiveCocycleExtMap I P (n+1) f = 0 ↔
      ∃ g : P ⟶ I.cocomplex.X n, g ≫ I.cocomplex.d n (n+1) = f.val :=
  I.extMk_eq_zero_iff f.val (n+1+1) rfl f.property n rfl

end LinearStudy
