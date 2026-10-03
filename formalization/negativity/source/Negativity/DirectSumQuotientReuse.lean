module
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

@[expose] public section
namespace Negativity
open scoped DirectSum
universe u v w
noncomputable section
variable {κ : Type u} {A : κ → Type v} {B : κ → Type w}
  [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]

/-- Exactness of componentwise additive maps is preserved by the actual
finitely supported direct sum. The preimage uses only the finite support. -/
theorem actual_direct_sum_map_range
    (b : ∀ n, A n →+ B n) (x : ⨁ n, B n) :
    x ∈ (DirectSum.map b).range ↔ ∀ n, x n ∈ (b n).range := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ n
    exact ⟨a n, DirectSum.map_apply b n a⟩
  · intro hx
    choose a ha using hx
    let z : ⨁ n, A n := ∑ n ∈ x.support, DirectSum.of A n (a n)
    refine ⟨z, ?_⟩
    change DirectSum.map b (∑ n ∈ x.support, DirectSum.of A n (a n)) = x
    rw [map_sum]
    simp only [DirectSum.map_of, ha]
    exact DirectSum.sum_support_of x

def actualDirectSumQuotientMap (b : ∀ n, A n →+ B n) :
    (⨁ n, B n) →+ ⨁ n, B n ⧸ (b n).range :=
  DirectSum.map (fun n => QuotientAddGroup.mk' (b n).range)

theorem actual_direct_sum_quotient_map_surjective (b : ∀ n, A n →+ B n) :
    Function.Surjective (actualDirectSumQuotientMap b) :=
  (DirectSum.map_surjective _).mpr (fun n => QuotientAddGroup.mk'_surjective _)

theorem actual_direct_sum_quotient_map_ker (b : ∀ n, A n →+ B n) :
    (actualDirectSumQuotientMap b).ker = (DirectSum.map b).range := by
  ext x
  rw [actual_direct_sum_map_range]
  change actualDirectSumQuotientMap b x = 0 ↔ _
  rw [DirectSum.ext_iff]
  simp only [actualDirectSumQuotientMap, DirectSum.map_apply, DFinsupp.zero_apply]
  exact forall_congr' (fun n => QuotientAddGroup.eq_zero_iff (x n))

/-- The quotient of the direct sum by actual summed boundaries is the
direct sum of the actual component quotients. This is constructed from
the genuine surjective quotient map and its proved kernel. -/
def actualDirectSumQuotientEquiv (b : ∀ n, A n →+ B n) :
    (⨁ n, B n) ⧸ (DirectSum.map b).range ≃+
      ⨁ n, B n ⧸ (b n).range :=
  QuotientAddGroup.liftEquiv _ (actual_direct_sum_quotient_map_surjective b)
    (actual_direct_sum_quotient_map_ker b).symm

@[simp]
theorem actualDirectSumQuotientEquiv_mk (b : ∀ n, A n →+ B n)
    (x : ⨁ n, B n) :
    actualDirectSumQuotientEquiv b (QuotientAddGroup.mk' _ x) =
      actualDirectSumQuotientMap b x := rfl

#print axioms actual_direct_sum_map_range
#print axioms actual_direct_sum_quotient_map_ker
#print axioms actualDirectSumQuotientEquiv
end
end Negativity
