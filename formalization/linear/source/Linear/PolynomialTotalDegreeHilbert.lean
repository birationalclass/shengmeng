module
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.NatCard
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Polynomial.HilbertPoly
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Add a slack exponent: degree at most N becomes degree exactly N. -/
def totalDegreeSlackEquiv (s N : ℕ) :
    {a : Fin s → ℕ // ∑ i, a i ≤ N} ≃
    {b : Option (Fin s) → ℕ // ∑ i, b i = N} where
  toFun a := ⟨fun i => i.elim (N - ∑ j, a.val j) a.val, by
    simpa [Fintype.sum_option] using Nat.sub_add_cancel a.property⟩
  invFun b := ⟨fun i => b.val (some i), by
    have h := b.property
    rw [Fintype.sum_option] at h
    change (∑ i, b.val (some i)) ≤ N
    omega⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    rfl
  right_inv b := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
        have h := b.property
        rw [Fintype.sum_option] at h
        dsimp
        omega
    | some i => rfl

/-- Count the actual monomial basis, including the zero-degree case. -/
theorem totalDegreeMonomials_natCard (s N : ℕ) :
    Nat.card {a : Fin s →₀ ℕ // a.sum (fun _ e => e) ≤ N} =
      (N + s).choose s := by
  let e : {a : Fin s →₀ ℕ // a.sum (fun _ e => e) ≤ N} ≃
      {a : Fin s → ℕ // ∑ i, a i ≤ N} :=
    Finsupp.equivFunOnFinite.subtypeEquiv (by simp [Finsupp.sum_fintype])
  rw [Nat.card_congr (e.trans (totalDegreeSlackEquiv s N))]
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Option (Fin s)) N)]
  rw [Sym.natCard_sym_eq_choose]
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin]
  have heq : s + 1 + N - 1 = N + s := by omega
  rw [heq]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- Exact dimension of polynomials in s variables of total degree at most N. -/
theorem polynomial_restrictTotalDegree_finrank
    (K : Type*) [Field K] (s N : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin s) K N) =
      (N + s).choose s := by
  change Module.finrank K (MvPolynomial.restrictSupport K
    {a : Fin s →₀ ℕ | a.sum (fun _ e => e) ≤ N}) = _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)]
  exact totalDegreeMonomials_natCard s N

/-- The cumulative polynomial for the actual source filtration, not an assumed growth model. -/
theorem polynomial_restrictTotalDegree_hilbert_eval
    (K : Type*) [Field K] (s N : ℕ) :
    (Polynomial.preHilbertPoly ℚ s 0).eval (N : ℚ) =
      Module.finrank K (MvPolynomial.restrictTotalDegree (Fin s) K N) := by
  rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ s (Nat.zero_le _)]
  simp only [Nat.sub_zero, polynomial_restrictTotalDegree_finrank]

end LinearStudy
