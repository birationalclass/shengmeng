module
public import Linear.UniversalDifference
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace LinearStudy
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem polynomial_diagonal_difference_degree (p : MvPolynomial ι K) :
    ∃ a : ι → MvPolynomial (ι ⊕ ι) K,
      MvPolynomial.rename Sum.inl p - MvPolynomial.rename Sum.inr p =
        ∑ i, a i * (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) ∧
      (∀ i, polynomialDoubleDiagonal (a i) = MvPolynomial.pderiv i p) ∧
      (∀ i, (a i).totalDegree ≤ p.totalDegree - 1) ∧
      (p.totalDegree = 0 → ∀ i, a i = 0) := by
  classical
  induction p using MvPolynomial.induction_on'' with
  | C c =>
    refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> simp
  | monomial_add m c p hm hc hp hmono =>
    obtain ⟨a, ha, hda, hga, hza⟩ := hmono
    obtain ⟨b, hb, hdb, hgb, hzb⟩ := hp
    have hdis : Disjoint (MvPolynomial.monomial m c : MvPolynomial ι K).support p.support := by
      simp [MvPolynomial.support_monomial, hc, Finset.disjoint_singleton_left]
      simpa [Finsupp.mem_support_iff] using hm
    have hs : (MvPolynomial.monomial m c + p).support =
        (MvPolynomial.monomial m c).support ∪ p.support := Finsupp.support_add_eq hdis
    have hg1 : (MvPolynomial.monomial m c).totalDegree ≤
        (MvPolynomial.monomial m c + p).totalDegree :=
      MvPolynomial.totalDegree_le_of_support_subset (by rw [hs]; exact Finset.subset_union_left)
    have hg2 : p.totalDegree ≤ (MvPolynomial.monomial m c + p).totalDegree :=
      MvPolynomial.totalDegree_le_of_support_subset (by rw [hs]; exact Finset.subset_union_right)
    refine ⟨fun i => a i + b i, ?_, ?_, ?_, ?_⟩
    · simp only [map_add, add_mul, Finset.sum_add_distrib]
      rw [← ha, ← hb]
      ring
    · intro i; simp [hda i, hdb i]
    · intro i
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le ((hga i).trans (Nat.sub_le_sub_right hg1 1))
          ((hgb i).trans (Nat.sub_le_sub_right hg2 1)))
    · intro hz i
      have hz1 := hza (Nat.eq_zero_of_le_zero (hg1.trans hz.le)) i
      have hz2 := hzb (Nat.eq_zero_of_le_zero (hg2.trans hz.le)) i
      simp [hz1, hz2]
  | mul_X p j hp =>
    by_cases hp0 : p = 0
    · subst p
      refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩ <;> simp
    obtain ⟨a, ha, hda, hga, hza⟩ := hp
    let u : MvPolynomial (ι ⊕ ι) K := MvPolynomial.rename Sum.inl p
    let b : ι → MvPolynomial (ι ⊕ ι) K := fun i =>
      u * (if i = j then 1 else 0) + MvPolynomial.X (Sum.inr j) * a i
    have hdeg : (p * MvPolynomial.X j).totalDegree = p.totalDegree + 1 := by
      rw [MvPolynomial.totalDegree_mul_of_isDomain hp0 (MvPolynomial.X_ne_zero j), MvPolynomial.totalDegree_X]
    refine ⟨b, ?_, ?_, ?_, ?_⟩
    · simp only [b, u, map_mul, add_mul, Finset.sum_add_distrib]
      have hfirst : (∑ i, MvPolynomial.rename Sum.inl p * (if i = j then 1 else 0) *
          (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i))) =
          MvPolynomial.rename Sum.inl p * (MvPolynomial.X (Sum.inl j) - MvPolynomial.X (Sum.inr j)) := by simp
      rw [hfirst]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← ha]
      simp
      ring
    · intro i
      simp only [b, map_add, map_mul, hda]
      rw [show polynomialDoubleDiagonal u = p from polynomialDoubleDiagonal_left p]
      by_cases hij : i = j
      · subst i; simp [polynomialDoubleDiagonal, Derivation.leibniz]
      · simp [hij, polynomialDoubleDiagonal, Derivation.leibniz]
    · intro i
      rw [hdeg]
      simp only [Nat.add_sub_cancel]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le
      · by_cases hij : i = j
        · simpa [hij, u] using MvPolynomial.totalDegree_rename_le Sum.inl p
        · simp [hij]
      · by_cases hz : p.totalDegree = 0
        · simp [hza hz i]
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by
            rw [MvPolynomial.totalDegree_X]
            have hg := hga i
            omega)
    · intro hz
      rw [hdeg] at hz
      omega

theorem polynomial_universal_difference_matrix_degree (P : ι → MvPolynomial ι K) :
    ∃ D : Matrix ι ι (MvPolynomial (ι ⊕ ι) K),
      D.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
        (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i)) ∧
      (∀ i j, polynomialDoubleDiagonal (D i j) = MvPolynomial.pderiv j (P i)) ∧
      ∀ i j, (D i j).totalDegree ≤ (P i).totalDegree - 1 := by
  choose D hD hd hdeg _ using fun i => polynomial_diagonal_difference_degree (P i)
  let M : Matrix ι ι (MvPolynomial (ι ⊕ ι) K) := D
  refine ⟨M, ?_, hd, hdeg⟩
  funext i
  simpa [M, Matrix.mulVec, dotProduct] using (hD i).symm

theorem polynomial_matrix_det_degree {σ : Type*}
    (M : Matrix ι ι (MvPolynomial σ K)) (d : ι → ℕ)
    (h : ∀ i j, (M i j).totalDegree ≤ d i) :
    M.det.totalDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  have hp : (∏ i, M (e i) i).totalDegree ≤ ∑ i, d (e i) :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans
      (Finset.sum_le_sum fun i _ => h (e i) i)
  rw [Equiv.sum_comp e d] at hp
  have hs : (Equiv.Perm.sign e • ∏ i, M (e i) i).totalDegree ≤
      (∏ i, M (e i) i).totalDegree := by
    have hsign : Equiv.Perm.sign e = 1 ∨ Equiv.Perm.sign e = -1 :=
      Int.units_eq_one_or e.sign
    rcases hsign with hs | hs <;> simp [hs]
  exact hs.trans hp

theorem polynomial_universal_difference_determinant_degree (P : ι → MvPolynomial ι K) :
    ∃ D : Matrix ι ι (MvPolynomial (ι ⊕ ι) K),
      D.mulVec (fun i => MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr i)) =
        (fun i => MvPolynomial.rename Sum.inl (P i) - MvPolynomial.rename Sum.inr (P i)) ∧
      (∀ i j, polynomialDoubleDiagonal (D i j) = MvPolynomial.pderiv j (P i)) ∧
      D.det.totalDegree ≤ ∑ i, ((P i).totalDegree - 1) := by
  obtain ⟨D, hD, hd, hdeg⟩ := polynomial_universal_difference_matrix_degree P
  exact ⟨D, hD, hd, polynomial_matrix_det_degree D (fun i => (P i).totalDegree - 1) hdeg⟩

end LinearStudy
