module
public import Linear.PolynomialDifferenceDegree
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

/-- Coefficient support proves the actual degree drop of each partial
derivative, including constants and the zero polynomial. -/
theorem polynomial_partial_derivative_totalDegree
    {K σ : Type*} [CommRing K] (P : MvPolynomial σ K) (j : σ) :
    (MvPolynomial.pderiv j P).totalDegree ≤ P.totalDegree-1 := by
  classical
  rw [MvPolynomial.totalDegree,Finset.sup_le_iff]
  intro s hs
  have hc := MvPolynomial.mem_support_iff.mp hs
  rw [MvPolynomial.coeff_pderiv] at hc
  have hP : s + Finsupp.single j 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hd := MvPolynomial.le_totalDegree hP
  change s.degree ≤ P.totalDegree-1
  change (s+Finsupp.single j 1).degree ≤ P.totalDegree at hd
  simp only [map_add,Finsupp.degree_single] at hd
  omega

/-- The SAME normal Jacobian has the fixed c(q-1) upper bound as soon as
the actual ambient equations have degree at most q. -/
theorem polynomial_normal_jacobian_totalDegree
    {K : Type*} [Field K] {r c q : ℕ}
    (P : (Fin r ⊕ Fin c) → MvPolynomial (Fin r ⊕ Fin c) K)
    (hP : ∀ i, (P i).totalDegree ≤ q) :
    (Matrix.det (fun i j => MvPolynomial.pderiv (Sum.inr j) (P (Sum.inr i)))).totalDegree ≤
      c*(q-1) := by
  have hd := polynomial_matrix_det_degree
    (fun i j => MvPolynomial.pderiv (Sum.inr j) (P (Sum.inr i)))
    (fun _ : Fin c => q-1) (fun i j =>
      (polynomial_partial_derivative_totalDegree _ _).trans (Nat.sub_le_sub_right (hP (Sum.inr i)) 1))
  simpa using hd

end LinearStudy
