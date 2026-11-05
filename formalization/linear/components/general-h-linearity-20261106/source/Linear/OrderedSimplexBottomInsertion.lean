module
public import Linear.ModuleOrderedBaseCech
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry.Scheme.Modules
universe u
variable {ι : Type u} [LinearOrder ι] [OrderBot ι]
/-- Prepend the actual least vertex to a strictly increasing tuple when absent. -/
def orderedSimplexPrependBottom {n : ℕ} (a : OrderedCechIndex ι n) (h : ⊥ < a.1 0) :
    OrderedCechIndex ι (n+1) :=
  ⟨Fin.cons ⊥ a.1,by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h
    · simpa using (Fin.strictMono_iff_lt_succ.mp a.2 j)⟩
/-- Its first face is the SAME original tuple. -/
theorem orderedSimplexPrependBottom_delete_zero {n : ℕ}
    (a : OrderedCechIndex ι n) (h : ⊥ < a.1 0) :
    (orderedSimplexPrependBottom a h).delete 0 = a := by
  apply Subtype.ext
  funext j
  change (Fin.cons ⊥ a.1 : Fin (n+2) → ι) (Fin.succAbove 0 j) = a.1 j
  simp
/-- Every face of a tuple strictly above the least vertex is still above it. -/
theorem orderedSimplexBottom_lt_delete_head {n : ℕ}
    (a : OrderedCechIndex ι (n+1)) (h : ⊥ < a.1 0) (k : Fin (n+2)) :
    ⊥ < (a.delete k).1 0 :=
  h.trans_le (a.2.monotone (Fin.zero_le _))
/-- The remaining faces commute with least-vertex insertion. -/
theorem orderedSimplexPrependBottom_delete_succ {n : ℕ}
    (a : OrderedCechIndex ι (n+1)) (h : ⊥ < a.1 0) (k : Fin (n+2)) :
    (orderedSimplexPrependBottom a h).delete k.succ =
      orderedSimplexPrependBottom (a.delete k) (orderedSimplexBottom_lt_delete_head a h k) := by
  apply Subtype.ext
  funext j
  change (Fin.cons ⊥ a.1 : Fin (n+3) → ι) (k.succ.succAbove j) =
    (Fin.cons ⊥ ((a.delete k).1) : Fin (n+2) → ι) j
  refine Fin.cases ?_ (fun l => ?_) j
  · simp
  · simp [OrderedCechIndex.delete,SimplexCategory.δ]
end LinearStudy
