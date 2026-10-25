module
public import Linear.FirstSyzygy
public import Mathlib.Tactic
/-! Actual degree-controlled affine ideal representations from regular highest homogeneous parts. The highest component of an affine ideal relation belongs to the highest-part ideal; no filtered comparison is supplied as an assumption. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
variable {K ι : Type*} [Field K]

theorem polynomial_zero_or_degree_lt_of_top_zero (p : MvPolynomial ι K) (n : ℕ)
    (hp : p.totalDegree ≤ n) (hz : MvPolynomial.homogeneousComponent n p = 0) :
    p = 0 ∨ p.totalDegree < n := by
  by_cases hn : 0 < n
  · right
    simpa [hz] using totalDegree_strip_top p n hn hp
  · left
    have hn0 : n = 0 := by omega
    subst n
    have hh := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := ι) (R := K)).mp
      (Nat.eq_zero_of_le_zero hp)
    rw [MvPolynomial.homogeneousComponent_eq_self hh] at hz
    exact hz

theorem homogeneousComponent_mul_top (a p : MvPolynomial ι K) (A B : ℕ)
    (ha : a.totalDegree ≤ A) (hp : p.totalDegree ≤ B) :
    MvPolynomial.homogeneousComponent (A + B) (a * p) =
      MvPolynomial.homogeneousComponent A a * MvPolynomial.homogeneousComponent B p := by
  let u := MvPolynomial.homogeneousComponent A a
  have hur : MvPolynomial.homogeneousComponent A (a - u) = 0 := by
    dsimp [u]
    rw [map_sub, MvPolynomial.homogeneousComponent_eq_self
      (MvPolynomial.homogeneousComponent_isHomogeneous A a), sub_self]
  have hdeg : (a - u).totalDegree ≤ A := (MvPolynomial.totalDegree_sub _ _).trans
    (max_le ha (MvPolynomial.homogeneousComponent_isHomogeneous A a).totalDegree_le)
  have hr : MvPolynomial.homogeneousComponent (A + B) ((a - u) * p) = 0 := by
    obtain hzero | hlt := polynomial_zero_or_degree_lt_of_top_zero (a - u) A hdeg hur
    · simp [hzero]
    · apply MvPolynomial.homogeneousComponent_eq_zero
      exact lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _)
        (Nat.add_lt_add_of_lt_of_le hlt hp)
  have he : a * p = (a - u) * p + u * p := by ring
  rw [he, map_add, hr, zero_add, mul_comm u p,
    homogeneousComponent_mul_homogeneous _ _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous A a),
    ite_eq_left (Nat.le_add_right A B), Nat.add_sub_cancel_left]
  exact mul_comm _ _

theorem skew_polynomial_relation_zero {n : ℕ} (P : Fin n → MvPolynomial ι K)
    (c : Fin n → Fin n → MvPolynomial ι K)
    (hs : ∀ i j, c i j = -c j i) (hd : ∀ i, c i i = 0) :
    ∑ i, (∑ j, c i j * P j) * P i = 0 := by
  classical
  -- Ordered pairs avoid any assumption that 2 is invertible.
  have hp : ∀ i j, c i j * P j * P i =
      (if i < j then c i j * P j * P i else 0) -
      (if j < i then c j i * P i * P j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst j; simp [hd]
    · simp only [ite_eq_left h, ite_eq_right (not_lt_of_ge h.le), hs i j]
      ring
  rw [show (∑ i, (∑ j, c i j * P j) * P i) = ∑ i, ∑ j, c i j * P j * P i by
    simp only [Finset.sum_mul]]
  calc
    _ = ∑ i, ∑ j, ((if i < j then c i j * P j * P i else 0) -
        (if j < i then c j i * P i * P j else 0)) := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      exact hp i j
    _ = (∑ i, ∑ j, if i < j then c i j * P j * P i else 0) -
        (∑ i, ∑ j, if j < i then c j i * P i * P j else 0) := by
      simp only [Finset.sum_sub_distrib]
    _ = 0 := by
      have he : (∑ i, ∑ j, if j < i then c j i * P i * P j else 0) =
          (∑ i, ∑ j, if i < j then c i j * P j * P i else 0) := Finset.sum_comm
      rw [he, sub_self]

theorem polynomial_representation_lower_peak {n : ℕ}
    (P : Fin n → MvPolynomial ι K)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial ι K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (f : MvPolynomial ι K) (N : ℕ) (hf : f.totalDegree < N)
    (a : Fin n → MvPolynomial ι K) (ha : ∑ i, a i * P i = f)
    (hb : ∀ i, a i = 0 ∨ (a i).totalDegree + (P i).totalDegree ≤ N) :
    ∃ b : Fin n → MvPolynomial ι K, (∑ i, b i * P i) = f ∧
      ∀ i, b i = 0 ∨ (b i).totalDegree + (P i).totalDegree < N := by
  classical
  let e := fun i => (P i).totalDegree
  let H := fun i => MvPolynomial.homogeneousComponent (e i) (P i)
  let A := fun i => if e i ≤ N then MvPolynomial.homogeneousComponent (N - e i) (a i) else 0
  have hab : ∀ i, e i ≤ N → (a i).totalDegree ≤ N - e i := by
    intro i hi
    obtain hz | hbound := hb i
    · simp [hz]
    · dsimp [e] at hi ⊢; omega
  have haz : ∀ i, ¬e i ≤ N → a i = 0 := by
    intro i hi
    obtain hz | hbound := hb i
    · exact hz
    · dsimp [e] at hi; omega
  have hterm : ∀ i, MvPolynomial.homogeneousComponent N (a i * P i) = A i * H i := by
    intro i
    by_cases hi : e i ≤ N
    · dsimp [A, H]
      rw [ite_eq_left hi]
      simpa only [Nat.sub_add_cancel hi] using
        homogeneousComponent_mul_top (a i) (P i) (N - e i) (e i) (hab i hi) le_rfl
    · simp [A, haz i hi, hi]
  have hrel : ∑ i, A i * H i = 0 := by
    have hh := congrArg (MvPolynomial.homogeneousComponent N) ha
    simpa only [map_sum, hterm, MvPolynomial.homogeneousComponent_eq_zero N f hf] using hh
  obtain ⟨c, hs, hd, hch, hc⟩ := homogeneous_first_syzygy_skew H e
    (fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _) hreg A N
    (fun i => by dsimp [A]; split_ifs <;> first
      | exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
      | exact MvPolynomial.isHomogeneous_zero ι K _)
    (fun i hi => by simp [A, hi]) hrel
  let b := fun i => a i - ∑ j, c i j * P j
  refine ⟨b, ?_, ?_⟩
  · dsimp [b]
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [ha, skew_polynomial_relation_zero P c hs hd, sub_zero]
  · intro i
    by_cases hi : e i ≤ N
    · have hsumdeg : (∑ j, c i j * P j).totalDegree ≤ N - e i := by
        apply MvPolynomial.totalDegree_finsetSum_le
        intro j hj
        by_cases hij : e i + e j ≤ N
        · have hdegree := (hch i j).1.totalDegree_le
          apply (MvPolynomial.totalDegree_mul _ _).trans
          dsimp [e] at hij hdegree ⊢
          omega
        · simp [(hch i j).2 hij]
      have hbdeg : (b i).totalDegree ≤ N - e i :=
        (MvPolynomial.totalDegree_sub _ _).trans (max_le (hab i hi) hsumdeg)
      have htop : MvPolynomial.homogeneousComponent (N - e i) (b i) = 0 := by
        dsimp [b]
        rw [map_sub, map_sum]
        have hai : MvPolynomial.homogeneousComponent (N - e i) (a i) = A i := by
          simp [A, hi]
        rw [hai, hc i]
        apply sub_eq_zero.mpr
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : e i + e j ≤ N
        · rw [mul_comm (c i j) (P j), homogeneousComponent_mul_homogeneous _ _ _ _ (hch i j).1,
            ite_eq_left (Nat.sub_le (N - e i) (e j)), Nat.sub_sub_self (by omega)]
          exact mul_comm _ _
        · simp [(hch i j).2 hij]
      obtain hz | hlt := polynomial_zero_or_degree_lt_of_top_zero (b i) (N - e i) hbdeg htop
      · exact Or.inl hz
      · right; dsimp [e] at hi hlt ⊢; omega
    · have hz := haz i hi
      have hcz : ∀ j, c i j = 0 := fun j => (hch i j).2 (by omega)
      left
      simp [b, hz, hcz]

theorem affine_ideal_degree_bounded_representation {n : ℕ}
    (P : Fin n → MvPolynomial ι K)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial ι K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (f : MvPolynomial ι K) (hf : f ∈ Ideal.span (Set.range P)) :
    ∃ a : Fin n → MvPolynomial ι K, (∑ i, a i * P i) = f ∧
      ∀ i, a i = 0 ∨ (a i).totalDegree + (P i).totalDegree ≤ f.totalDegree := by
  classical
  have hreduce : ∀ N : ℕ, ∀ a : Fin n → MvPolynomial ι K,
      (∑ i, a i * P i) = f →
      (∀ i, a i = 0 ∨ (a i).totalDegree + (P i).totalDegree ≤ N) →
      ∃ b : Fin n → MvPolynomial ι K, (∑ i, b i * P i) = f ∧
        ∀ i, b i = 0 ∨ (b i).totalDegree + (P i).totalDegree ≤ f.totalDegree := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro a ha hb
      by_cases hN : N ≤ f.totalDegree
      · exact ⟨a, ha, fun i => (hb i).imp_right (fun hi => hi.trans hN)⟩
      · have hNpos : 0 < N := by omega
        obtain ⟨b, he, hbound⟩ := polynomial_representation_lower_peak P hreg f N
          (Nat.lt_of_not_ge hN) a ha hb
        apply ih (N - 1) (by omega) b he
        intro i
        obtain hz | hb' := hbound i
        · exact Or.inl hz
        · exact Or.inr (by omega)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  let N := Finset.univ.sup (fun i => (a i).totalDegree + (P i).totalDegree)
  apply hreduce N a ha
  intro i
  right
  exact Finset.le_sup (f := fun i => (a i).totalDegree + (P i).totalDegree)
    (Finset.mem_univ i)

theorem affine_ideal_top_component_mem {n : ℕ}
    (P : Fin n → MvPolynomial ι K)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial ι K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (f : MvPolynomial ι K) (hf : f ∈ Ideal.span (Set.range P))
    (N : ℕ) (hN : f.totalDegree ≤ N) :
    MvPolynomial.homogeneousComponent N f ∈ Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))) := by
  classical
  obtain ⟨a, ha, hb⟩ := affine_ideal_degree_bounded_representation P hreg f hf
  have he := congrArg (MvPolynomial.homogeneousComponent N) ha
  rw [map_sum] at he
  rw [← he]
  apply Ideal.sum_mem
  intro i hi
  obtain hz | hb' := hb i
  · simp [hz]
  · have hei : (P i).totalDegree ≤ N := by omega
    have hai : (a i).totalDegree ≤ N - (P i).totalDegree := by omega
    rw [show MvPolynomial.homogeneousComponent N (a i * P i) =
      MvPolynomial.homogeneousComponent (N - (P i).totalDegree) (a i) *
        MvPolynomial.homogeneousComponent (P i).totalDegree (P i) from
      by simpa only [Nat.sub_add_cancel hei] using
        homogeneousComponent_mul_top (a i) (P i) (N - (P i).totalDegree) (P i).totalDegree hai le_rfl]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

end LinearStudy
