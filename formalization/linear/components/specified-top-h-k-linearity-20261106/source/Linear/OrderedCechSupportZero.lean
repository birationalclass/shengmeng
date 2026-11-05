module
public import Linear.OrderedCechSupportContraction
public import Linear.ModuleOrderedCechAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R] {ι : Type v} [LinearOrder ι]

private def zeroCechPair (i j : ι) (h : i < j) :
    Scheme.Modules.OrderedCechIndex ι 1 :=
  ⟨![i,j],by
    apply Fin.strictMono_iff_lt_succ.2
    intro k
    fin_cases k
    exact h⟩

private theorem zeroCechPair_delete_zero (i j : ι) (h : i < j) :
    (zeroCechPair i j h).delete 0 = Scheme.Modules.orderedCechSingleton j := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

private theorem zeroCechPair_delete_one (i j : ι) (h : i < j) :
    (zeroCechPair i j h).delete 1 = Scheme.Modules.orderedCechSingleton i := by
  apply Subtype.ext
  funext k
  fin_cases k
  rfl

/-- A zero cocycle in the actual deletion complex has a single coefficient
on every singleton, including when the support condition is nonempty. -/
theorem orderedCechSupport_zeroCycle_constant (N : Set ι) (j : ι)
    (s : OrderedCechSupportCochain R N 0)
    (hs : orderedCechSupportDifferential R N 0 s = 0) :
    ∀ a, s.1 a = s.1 (Scheme.Modules.orderedCechSingleton j) := by
  have hpair (i k : ι) (hik : i < k) :
      s.1 (Scheme.Modules.orderedCechSingleton k) =
        s.1 (Scheme.Modules.orderedCechSingleton i) := by
    have h := congrArg (fun t => t.1 (zeroCechPair i k hik)) hs
    change (∑ l : Fin 2, (-1 : R) ^ (l : ℕ) *
      s.1 ((zeroCechPair i k hik).delete l)) = 0 at h
    simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,pow_zero,pow_one,
      one_mul,neg_one_mul,zeroCechPair_delete_zero,zeroCechPair_delete_one,
      ← sub_eq_add_neg] at h
    exact sub_eq_zero.mp h
  intro a
  have ha : a = Scheme.Modules.orderedCechSingleton (a.1 0) := by
    apply Subtype.ext
    funext k
    have hk : k = (0 : Fin (0+1)) := Fin.ext (by omega)
    subst k
    rfl
  rw [ha]
  rcases lt_trichotomy j (a.1 0) with h | h | h
  · exact hpair j (a.1 0) h
  · rw [h]
  · exact (hpair (a.1 0) j h).symm

/-- A nonempty required support with a missing index has no nonzero
zero cocycle. This is the degree-zero coefficient test used to remove
negative Laurent exponents from a global projective section. -/
theorem orderedCechSupport_zeroCycle_eq_zero (N : Set ι)
    (hN : N.Nonempty) (j : ι) (hj : j ∉ N)
    (s : OrderedCechSupportCochain R N 0)
    (hs : orderedCechSupportDifferential R N 0 s = 0) : s = 0 := by
  have hj0 : s.1 (Scheme.Modules.orderedCechSingleton j) = 0 := by
    apply s.2
    intro h
    obtain ⟨i,hi⟩ := hN
    obtain ⟨k,hk⟩ := h hi
    have hji : j = i := hk
    exact hj (hji.symm ▸ hi)
  apply Subtype.ext
  funext a
  change s.1 a = 0
  rw [orderedCechSupport_zeroCycle_constant N j s hs a,hj0]
end LinearStudy
