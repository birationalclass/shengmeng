module
public import Linear.OrderedConstantCechBottomContraction
public import Mathlib.Data.Fintype.Order
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry.Scheme.Modules
universe u v
/-- Every FINITE ordered simplex,including an empty vertex type,has zero positive
constant-coefficient cohomology,for ANY abelian coefficient group. -/
theorem orderedConstantCech_finite_exists_boundary {ι : Type u} [LinearOrder ι] [Finite ι]
    {M : Type v} [AddCommGroup M] (n : ℕ) (s : OrderedCechIndex ι (n+1) → M)
    (hs : ∀ a,orderedConstantCechDifferential (n+1) s a = 0) :
    ∃ t : OrderedCechIndex ι n → M,∀ a,orderedConstantCechDifferential n t a = s a := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    exact ⟨0,fun a => isEmptyElim (a.1 0)⟩
  | inr h =>
    letI := h
    letI := Fintype.ofFinite ι
    letI := Fintype.toOrderBot ι
    exact orderedConstantCech_exists_boundary n s hs
/-- The original single-vertex ordered tuple. -/
def orderedSimplexSingleton {ι : Type u} [Preorder ι] (i : ι) : OrderedCechIndex ι 0 :=
  ⟨fun _ => i,by
    intro a b h
    have hab : a = b := Fin.ext (by omega)
    subst b
    exact False.elim (lt_irrefl _ h)⟩
/-- At degree zero,cycles are SAME constant values;the augmentation target is not
an arbitrary replacement quotient. -/
theorem orderedConstantCech_zero_cocycle_constant {ι : Type u} [LinearOrder ι] [OrderBot ι]
    {M : Type v} [AddCommGroup M] (s : OrderedCechIndex ι 0 → M)
    (hs : ∀ a,orderedConstantCechDifferential 0 s a = 0) :
    ∃ m : M,∀ a,s a = m := by
  let b := orderedSimplexSingleton (⊥ : ι)
  refine ⟨s b,fun a => ?_⟩
  by_cases ha : ⊥ < a.1 0
  · have hb : (orderedSimplexPrependBottom a ha).delete (1 : Fin 2) = b := by
      apply Subtype.ext
      funext j
      have hj : j = 0 := Fin.ext (by omega)
      subst j
      rfl
    have hc := hs (orderedSimplexPrependBottom a ha)
    dsimp only [orderedConstantCechDifferential] at hc
    rw [Fin.sum_univ_two,orderedSimplexPrependBottom_delete_zero,hb] at hc
    exact sub_eq_zero.mp (by simpa only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,
      one_smul,neg_one_zsmul,sub_eq_add_neg] using hc)
  · have ha0 : a.1 0 = ⊥ := le_antisymm (le_of_not_gt ha) bot_le
    have hab : a = b := by
      apply Subtype.ext
      funext j
      have hj : j = 0 := Fin.ext (by omega)
      subst j
      exact ha0
    rw [hab]
end LinearStudy
