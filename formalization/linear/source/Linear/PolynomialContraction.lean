module
public import Linear.AffineFunctional
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Tactic
/-! Actual double-polynomial tensor contraction under a low-degree vanishing functional. The total-degree bound forces the contraction to be a scalar. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped TensorProduct
namespace LinearStudy
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem polynomial_double_monomial_split (a b : ι →₀ ℕ) (c : K) :
    MvPolynomial.monomial (a.sumElim b) c =
      MvPolynomial.rename Sum.inl (MvPolynomial.monomial a c) *
      MvPolynomial.rename Sum.inr (MvPolynomial.monomial b (1 : K)) := by
  rw [MvPolynomial.rename_monomial, MvPolynomial.rename_monomial,
    MvPolynomial.monomial_mul_monomial, mul_one, Finsupp.sumElim_eq_add]

omit [Fintype ι] [DecidableEq ι] in
theorem polynomial_double_monomial_contraction
    (P : ι → MvPolynomial ι K)
    (ell : (MvPolynomial ι K ⧸ Ideal.span (Set.range P)) →ₗ[K] K)
    (a b : ι →₀ ℕ) (c : K) :
    tensorFunctionalContraction ell
      (polynomialDoubleTensorMap P (MvPolynomial.monomial (a.sumElim b) c)) =
      ell (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.monomial a c)) •
        Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.monomial b 1) := by
  rw [polynomial_double_monomial_split, map_mul,
    polynomialDoubleTensorMap_left, polynomialDoubleTensorMap_right,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_one, one_mul, tensorFunctionalContraction_tmul]

omit [DecidableEq ι] in
theorem polynomial_double_monomial_degree (a b : ι →₀ ℕ) :
    (a.sumElim b).degree = a.degree + b.degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Finsupp.sumElim_inl, Finsupp.sumElim_inr]

omit [Fintype ι] in
theorem polynomial_double_monomial_contraction_constant
    (P : ι → MvPolynomial ι K) (D : ℕ)
    (ell : (MvPolynomial ι K ⧸ Ideal.span (Set.range P)) →ₗ[K] K)
    (hv : ∀ f : MvPolynomial ι K, f.totalDegree < D →
      ell (Ideal.Quotient.mk (Ideal.span (Set.range P)) f) = 0)
    (a b : ι →₀ ℕ) (c : K) (hd : a.degree + b.degree ≤ D) :
    tensorFunctionalContraction ell
      (polynomialDoubleTensorMap P (MvPolynomial.monomial (a.sumElim b) c)) =
      algebraMap K (MvPolynomial ι K ⧸ Ideal.span (Set.range P))
        (ell (Ideal.Quotient.mk (Ideal.span (Set.range P))
          (polynomialDoubleRightPoint (0 : ι → K) (MvPolynomial.monomial (a.sumElim b) c)))) := by
  rw [polynomial_double_monomial_contraction]
  have he : polynomialDoubleRightPoint (0 : ι → K) (MvPolynomial.monomial (a.sumElim b) c) =
      MvPolynomial.monomial a c * MvPolynomial.C (if b = 0 then (1 : K) else 0) := by
    rw [polynomial_double_monomial_split, map_mul, polynomialDoubleRightPoint_left,
      polynomialDoubleRightPoint_right, MvPolynomial.eval_zero,
      MvPolynomial.constantCoeff_monomial]
  rw [he]
  by_cases hb : b = 0
  · subst b
    simp only [ite_true, mul_one, MvPolynomial.monomial_zero',
      map_one]
    exact (Algebra.algebraMap_eq_smul_one _).symm
  · have hbd : 0 < b.degree := Nat.pos_of_ne_zero (by
      intro hz; exact hb ((Finsupp.degree_eq_zero_iff b).mp hz))
    have hvan : ell (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.monomial a c)) = 0 :=
      hv _ (lt_of_le_of_lt (MvPolynomial.totalDegree_monomial_le a c) (by
        change a.degree < D; omega))
    simp [hb, hvan]

theorem polynomial_double_contraction_constant
    (P : ι → MvPolynomial ι K) (D : ℕ)
    (ell : (MvPolynomial ι K ⧸ Ideal.span (Set.range P)) →ₗ[K] K)
    (hv : ∀ f : MvPolynomial ι K, f.totalDegree < D →
      ell (Ideal.Quotient.mk (Ideal.span (Set.range P)) f) = 0)
    (p : MvPolynomial (ι ⊕ ι) K) (hp : p.totalDegree ≤ D) :
    tensorFunctionalContraction ell (polynomialDoubleTensorMap P p) =
      algebraMap K (MvPolynomial ι K ⧸ Ideal.span (Set.range P))
        (ell (Ideal.Quotient.mk (Ideal.span (Set.range P))
          (polynomialDoubleRightPoint (0 : ι → K) p))) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_rhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  let a := (Finsupp.sumFinsuppEquivProdFinsupp m).1
  let b := (Finsupp.sumFinsuppEquivProdFinsupp m).2
  have he : a.sumElim b = m := Finsupp.comapDomain_sumElim_comapDomain m
  simpa only [he] using polynomial_double_monomial_contraction_constant P D ell hv a b (p.coeff m)
    (by rw [← polynomial_double_monomial_degree, he]; exact (MvPolynomial.le_totalDegree hm).trans hp)

theorem polynomialDoubleRightZero_totalDegree
    (p : MvPolynomial (ι ⊕ ι) K) :
    (polynomialDoubleRightPoint (0 : ι → K) p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  let a := (Finsupp.sumFinsuppEquivProdFinsupp m).1
  let b := (Finsupp.sumFinsuppEquivProdFinsupp m).2
  have he : a.sumElim b = m := Finsupp.comapDomain_sumElim_comapDomain m
  have hmdeg : a.degree + b.degree ≤ p.totalDegree := by
    rw [← polynomial_double_monomial_degree, he]
    exact MvPolynomial.le_totalDegree hm
  have hmono : polynomialDoubleRightPoint (0 : ι → K) (MvPolynomial.monomial m (p.coeff m)) =
      MvPolynomial.monomial a (p.coeff m) * MvPolynomial.C (if b = 0 then (1 : K) else 0) := by
    rw [← he, polynomial_double_monomial_split, map_mul, polynomialDoubleRightPoint_left,
      polynomialDoubleRightPoint_right, MvPolynomial.eval_zero,
      MvPolynomial.constantCoeff_monomial]
  rw [hmono]
  by_cases hb : b = 0
  · simp only [hb, ite_true, MvPolynomial.C_1, mul_one]
    exact (MvPolynomial.totalDegree_monomial_le a (p.coeff m)).trans (by change a.degree ≤ p.totalDegree; omega)
  · simp [hb]

end LinearStudy
