module
public import Linear.FilteredIdeal
public import Mathlib.Tactic
/-! Highest homogeneous components of products, row-bounded determinants and polynomial coefficient equations. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
variable {K ι κ : Type*} [Field K]

theorem homogeneousComponent_prod_top [DecidableEq κ]
    (s : Finset κ) (p : κ → MvPolynomial ι K) (e : κ → ℕ)
    (hp : ∀ i ∈ s, (p i).totalDegree ≤ e i) :
    MvPolynomial.homogeneousComponent (∑ i ∈ s, e i) (∏ i ∈ s, p i) =
      ∏ i ∈ s, MvPolynomial.homogeneousComponent (e i) (p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi,
      homogeneousComponent_mul_top _ _ _ _ (hp i (Finset.mem_insert_self _ _))]
    · rw [ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]
    · exact (MvPolynomial.totalDegree_finsetProd _ _).trans
        (Finset.sum_le_sum (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem homogeneousComponent_det_top [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ (MvPolynomial ι K)) (e : κ → ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ e i) :
    MvPolynomial.homogeneousComponent (∑ i, e i) M.det =
      Matrix.det (fun i j => MvPolynomial.homogeneousComponent (e i) (M i j)) := by
  classical
  rw [Matrix.det_apply, map_sum, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro v hv
  have he := homogeneousComponent_prod_top Finset.univ (fun i => M (v i) i)
    (fun i => e (v i)) (fun i hi => hM _ _)
  rw [Equiv.sum_comp v e] at he
  have hs : Equiv.Perm.sign v = 1 ∨ Equiv.Perm.sign v = -1 := Int.units_eq_one_or v.sign
  rcases hs with hs | hs
  · simpa only [hs, one_smul] using he
  · simpa [hs] using congrArg Neg.neg he

theorem coefficient_matrix_top_equations [Fintype κ] [DecidableEq κ]
    (P : κ → MvPolynomial κ K) (e : κ → ℕ) (he : ∀ i, 0 < e i)
    (N : Matrix κ κ (MvPolynomial κ K))
    (hN : N.mulVec MvPolynomial.X =
      fun i => P i - MvPolynomial.C ((P i).constantCoeff)) :
    Matrix.mulVec (fun i j => MvPolynomial.homogeneousComponent (e i - 1) (N i j)) MvPolynomial.X =
      fun i => MvPolynomial.homogeneousComponent (e i) (P i) := by
  classical
  funext i
  have hh := congrArg (MvPolynomial.homogeneousComponent (e i)) (congrFun hN i)
  simp only [Matrix.mulVec, dotProduct, map_sum, map_sub] at hh
  have ht : ∀ j, MvPolynomial.homogeneousComponent (e i) (N i j * MvPolynomial.X j) =
      MvPolynomial.homogeneousComponent (e i - 1) (N i j) * MvPolynomial.X j := by
    intro j
    rw [homogeneousComponent_mul_homogeneous _ _ _ _ (MvPolynomial.isHomogeneous_X K j),
      ite_eq_left (by have h := he i; omega)]
  simp only [ht] at hh
  rw [MvPolynomial.homogeneousComponent_eq_zero (e i) (MvPolynomial.C ((P i).constantCoeff)) (by
    rw [MvPolynomial.totalDegree_C]; exact he i), sub_zero] at hh
  exact hh

end LinearStudy
