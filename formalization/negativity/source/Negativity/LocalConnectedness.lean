module

public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity

/-- The ring-theoretic contradiction in the connectedness argument: a local
ring has no nontrivial idempotent. Formal-functions geometry is a separate step. -/
theorem localRing_idempotent_trivial (R : Type*) [CommRing R] [IsLocalRing R]
    (a : R) (ha : a * a = a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · right
    apply hu.mul_left_cancel
    simpa using ha
  · left
    have h : (1 - a) * a = (1 - a) * 0 := by rw [mul_zero];linear_combination -ha
    exact hu.mul_left_cancel h

/-- A local ring cannot split into two nonzero rings. This is the algebraic
last step after a disconnected fiber has produced a product decomposition. -/
theorem localRing_not_product_nontrivial (R A B : Type*)
    [CommRing R] [IsLocalRing R] [CommRing A] [CommRing B]
    [Nontrivial A] [Nontrivial B] (e : R ≃+* A × B) : False := by
  let a := e.symm (1, 0)
  have ha : a * a = a := by apply e.injective;simp [a]
  rcases localRing_idempotent_trivial R a ha with hzero | hone
  · have h := congrArg (fun r => (e r).1) hzero
    simp [a] at h
  · have h := congrArg (fun r => (e r).2) hone
    simp [a] at h

end Negativity
