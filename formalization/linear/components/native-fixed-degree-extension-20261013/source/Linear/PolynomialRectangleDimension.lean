module
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Data.Finsupp.Fintype
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- The ACTUAL rectangular polynomial coefficient space has (N+1)^s
dimensions; its monomial indices are explicitly identified with bounded functions. -/
theorem polynomial_restrictDegree_finrank
    (k σ : Type*) [Field k] [Finite σ] (N : ℕ) :
    Module.finrank k (MvPolynomial.restrictDegree σ k N) = (N + 1) ^ Nat.card σ := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  let e : {v : σ →₀ ℕ // ∀ i, v i ≤ N} ≃ (σ → Fin (N + 1)) :=
    { toFun v i := ⟨v.val i, Nat.lt_succ_iff.mpr (v.property i)⟩
      invFun w := ⟨Finsupp.equivFunOnFinite.symm (fun i => (w i).val),
        fun i => Nat.lt_succ_iff.mp (w i).isLt⟩
      left_inv v := by apply Subtype.ext; ext i; rfl
      right_inv w := by funext i; apply Fin.ext; rfl }
  unfold MvPolynomial.restrictDegree
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport k
    {v : σ →₀ ℕ | ∀ i, v i ≤ N})]
  change Nat.card {v : σ →₀ ℕ // ∀ i, v i ≤ N} = _
  rw [Nat.card_congr e]
  simp [Nat.card_eq_fintype_card]

/-- Rectangular degrees at most N give ACTUAL total degree at most s*N. -/
theorem polynomial_restrictDegree_le_totalDegree
    (k σ : Type*) [Field k] [Finite σ] (N : ℕ) :
    MvPolynomial.restrictDegree σ k N ≤
      MvPolynomial.restrictTotalDegree σ k (Nat.card σ * N) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  intro p hp
  apply (MvPolynomial.mem_restrictTotalDegree σ _ p).mpr
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro v hv
  rw [Finsupp.sum_fintype]
  calc
    ∑ i : σ, v i ≤ ∑ _i : σ, N :=
      Finset.sum_le_sum (fun i _ => (MvPolynomial.mem_restrictDegree σ p N).mp hp v hv i)
    _ = Nat.card σ * N := by simp [Nat.card_eq_fintype_card]
  all_goals simp

end LinearStudy
