module
public import Linear.OrderedSimplexBottomInsertion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry.Scheme.Modules
universe u v
variable {ι : Type u} [LinearOrder ι] [OrderBot ι]
variable {M : Type v} [AddCommGroup M]
/-- Ordered constant-coefficient cochains use the ORIGINAL alternating deletion sum. -/
def orderedConstantCechDifferential (n : ℕ) (s : OrderedCechIndex ι n → M) :
    OrderedCechIndex ι (n+1) → M :=
  fun a => ∑ k : Fin (n+2), (-1 : ℤ) ^ (k : ℕ) • s (a.delete k)
/-- Least-vertex insertion,zero exactly when the vertex is already present. -/
def orderedConstantCechBottomContraction (n : ℕ) (s : OrderedCechIndex ι (n+1) → M) :
    OrderedCechIndex ι n → M :=
  fun a => if h : ⊥ < a.1 0 then s (orderedSimplexPrependBottom a h) else 0
/-- Deleting a nonfirst vertex preserves an existing least first vertex. -/
theorem orderedSimplex_delete_succ_head_eq_bottom {n : ℕ}
    (a : OrderedCechIndex ι (n+1)) (h : a.1 0 = ⊥) (k : Fin (n+1)) :
    (a.delete k.succ).1 0 = ⊥ := by
  change a.1 (k.succ.succAbove 0) = ⊥
  simpa using h
/-- Reinsert the deleted least first vertex to recover the SAME original tuple. -/
theorem orderedSimplexPrependBottom_delete_first {n : ℕ}
    (a : OrderedCechIndex ι (n+1)) (h : a.1 0 = ⊥)
    (ha : ⊥ < (a.delete 0).1 0) :
    orderedSimplexPrependBottom (a.delete 0) ha = a := by
  apply Subtype.ext
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact h.symm
  · change a.1 (Fin.succAbove 0 k) = a.1 k.succ
    simp
/-- Every positive-degree ordered cocycle with ANY abelian coefficient group is a
boundary when a least vertex exists.This is a pure simplex lemma,not yet a native
sheaf ordered/full Cech comparison. -/
theorem orderedConstantCech_exists_boundary (n : ℕ) (s : OrderedCechIndex ι (n+1) → M)
    (hs : ∀ a, orderedConstantCechDifferential (n+1) s a = 0) :
    ∃ t : OrderedCechIndex ι n → M, ∀ a, orderedConstantCechDifferential n t a = s a := by
  refine ⟨orderedConstantCechBottomContraction n s,fun a => ?_⟩
  by_cases ha : ⊥ < a.1 0
  · have hc := hs (orderedSimplexPrependBottom a ha)
    dsimp only [orderedConstantCechDifferential] at hc
    rw [Fin.sum_univ_succ] at hc
    simp only [Fin.val_zero,pow_zero,one_smul,orderedSimplexPrependBottom_delete_zero,
      Fin.val_succ,pow_succ,mul_neg_one,neg_smul,
      orderedSimplexPrependBottom_delete_succ,Finset.sum_neg_distrib] at hc
    have hh : orderedConstantCechDifferential n (orderedConstantCechBottomContraction n s) a =
        ∑ k : Fin (n+2), (-1 : ℤ) ^ (k : ℕ) •
          s (orderedSimplexPrependBottom (a.delete k) (orderedSimplexBottom_lt_delete_head a ha k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [orderedConstantCechBottomContraction,dif_pos (orderedSimplexBottom_lt_delete_head a ha k)]
    rw [← hh] at hc
    exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hc)).symm
  · have h0 : a.1 0 = ⊥ := le_antisymm (le_of_not_gt ha) bot_le
    have hz : ⊥ < (a.delete 0).1 0 := by
      change ⊥ < a.1 (Fin.succAbove 0 0)
      rw [← h0]
      apply a.2
      simp
    have hz' : orderedConstantCechBottomContraction n s (a.delete 0) = s a := by
      rw [orderedConstantCechBottomContraction,dif_pos hz,
        orderedSimplexPrependBottom_delete_first a h0 hz]
    dsimp only [orderedConstantCechDifferential]
    rw [Fin.sum_univ_succ,hz']
    simp only [Fin.val_zero,pow_zero,one_smul]
    have ht : ∑ k : Fin (n+1), (-1 : ℤ) ^ (k.succ : ℕ) •
        orderedConstantCechBottomContraction n s (a.delete k.succ) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk : ¬⊥ < (a.delete k.succ).1 0 := by
        rw [orderedSimplex_delete_succ_head_eq_bottom a h0 k]
        exact lt_irrefl _
      rw [orderedConstantCechBottomContraction,dif_neg hk,smul_zero]
    rw [ht,add_zero]
end LinearStudy
