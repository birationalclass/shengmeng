module
public import Linear.PolynomialOriginFinite
public import Linear.HomogeneousQuotient
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Tactic
/-! Highest-homogeneous-part reduction on actual affine polynomial quotients. The quotient is proved finite from the origin-only top zero locus. With positive degrees and regular highest parts, every class has a representative of degree at most sum(deg P_i-1). This does not assert affine Euler-Jacobi vanishing or geometric residue comparison. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
variable {K ι : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousComponent_mul_homogeneous (a p : MvPolynomial ι K) (n d : ℕ)
    (hp : p.IsHomogeneous d) :
    MvPolynomial.homogeneousComponent n (a * p) =
      if d ≤ n then MvPolynomial.homogeneousComponent (n - d) a * p else 0 := by
  have hh := DirectSum.coe_decompose_mul_of_right_mem (MvPolynomial.homogeneousSubmodule ι K)
    (a := a) (b := p) (i := d) n hp
  change (MvPolynomial.decomposition.decompose' (a * p) n : MvPolynomial ι K) =
    if d ≤ n then (MvPolynomial.decomposition.decompose' a (n - d) : MvPolynomial ι K) * p else 0 at hh
  simpa only [MvPolynomial.decomposition.decompose'_apply] using hh

theorem homogeneous_ideal_bounded_representation {κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial ι K) (d : κ → ℕ) (hP : ∀ i, (P i).IsHomogeneous (d i))
    (f : MvPolynomial ι K) (n : ℕ) (hf : f.IsHomogeneous n)
    (hI : f ∈ Ideal.span (Set.range P)) :
    ∃ a : κ → MvPolynomial ι K, (∑ i, a i * P i) = f ∧
      ∀ i, (a i).IsHomogeneous (n - d i) ∧ (¬d i ≤ n → a i = 0) := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hI
  let a := fun i => if d i ≤ n then MvPolynomial.homogeneousComponent (n - d i) (c i) else 0
  refine ⟨a, ?_, ?_⟩
  · have he := congrArg (MvPolynomial.homogeneousComponent n) hc
    rw [map_sum, MvPolynomial.homogeneousComponent_eq_self hf] at he
    convert he using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [homogeneousComponent_mul_homogeneous _ _ _ _ (hP i)]
    dsimp [a]
    split_ifs <;> simp
  · intro i
    dsimp [a]
    split_ifs with h
    · exact ⟨MvPolynomial.homogeneousComponent_isHomogeneous _ _, fun hn => (hn h).elim⟩
    · exact ⟨MvPolynomial.isHomogeneous_zero ι K _, fun _ => rfl⟩

theorem totalDegree_strip_top (p : MvPolynomial ι K) (n : ℕ) (hn : 0 < n)
    (hp : p.totalDegree ≤ n) :
    (p - MvPolynomial.homogeneousComponent n p).totalDegree < n := by
  classical
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hn]
  intro m hm
  by_contra hlt
  have hmn : n ≤ m.degree := Nat.le_of_not_gt hlt
  have hc : (p - MvPolynomial.homogeneousComponent n p).coeff m ≠ 0 :=
    Finsupp.mem_support_iff.mp hm
  apply hc
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_homogeneousComponent]
  change p.coeff m - (if m.degree = n then p.coeff m else 0) = 0
  by_cases he : m.degree = n
  · simp [he]
  · have hmgt : p.totalDegree < m.degree := lt_of_le_of_lt hp (lt_of_le_of_ne hmn (Ne.symm he))
    have hzero := MvPolynomial.coeff_eq_zero_of_totalDegree_lt hmgt
    simp [he, hzero]

theorem finite_polynomial_quotient_bounded_representatives
    (I : Ideal (MvPolynomial ι K)) [Module.Finite K (MvPolynomial ι K ⧸ I)] :
    ∃ B : ℕ, ∀ p : MvPolynomial ι K, ∃ r : MvPolynomial ι K,
      r.totalDegree ≤ B ∧ Ideal.Quotient.mk I p = Ideal.Quotient.mk I r := by
  classical
  let Q := MvPolynomial ι K ⧸ I
  let pi := Ideal.Quotient.mkₐ K I
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := K) (M := Q)
  choose a ha using fun i : Fin m => Ideal.Quotient.mk_surjective (s i)
  let B := Finset.univ.sup (fun i => (a i).totalDegree)
  refine ⟨B, ?_⟩
  intro p
  have hp : pi p ∈ Submodule.span K (Set.range s) := by rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hp
  refine ⟨∑ i, c i • a i, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    apply (MvPolynomial.totalDegree_smul_le _ _).trans
    change (a i).totalDegree ≤ Finset.univ.sup (fun k => (a k).totalDegree)
    exact Finset.le_sup (f := fun k : Fin m => (a k).totalDegree) hi
  · change pi p = pi (∑ i, c i • a i)
    rw [map_sum]
    simp only [map_smul]
    have haa : ∀ i, pi (a i) = s i := ha
    simpa only [haa] using hc.symm

theorem finite_homogeneous_ideal_contains_large_degree
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    [Module.Finite K (MvPolynomial ι K ⧸ I)] :
    ∃ B : ℕ, ∀ n : ℕ, B < n → ∀ p : MvPolynomial ι K,
      p.IsHomogeneous n → p ∈ I := by
  obtain ⟨B, hB⟩ := finite_polynomial_quotient_bounded_representatives I
  refine ⟨B, ?_⟩
  intro n hn p hp
  obtain ⟨r, hr, he⟩ := hB p
  have hm : p - r ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, he, sub_self]
  have ht := MvPolynomial.homogeneousComponent_mem_of_mem hI hm n
  rw [map_sub, MvPolynomial.homogeneousComponent_eq_self hp,
    MvPolynomial.homogeneousComponent_eq_zero n r (lt_of_le_of_lt hr hn), sub_zero] at ht
  exact ht

theorem polynomial_top_reduction {κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial ι K) (B : ℕ)
    (hB : ∀ n : ℕ, B < n → ∀ p : MvPolynomial ι K, p.IsHomogeneous n →
      p ∈ Ideal.span (Set.range (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (p : MvPolynomial ι K) (hp : B < p.totalDegree) :
    ∃ r : MvPolynomial ι K, r.totalDegree < p.totalDegree ∧
      Ideal.Quotient.mk (Ideal.span (Set.range P)) p =
        Ideal.Quotient.mk (Ideal.span (Set.range P)) r := by
  classical
  let N := p.totalDegree
  let e := fun i => (P i).totalDegree
  let H := fun i => MvPolynomial.homogeneousComponent (e i) (P i)
  let f := MvPolynomial.homogeneousComponent N p
  have hf := MvPolynomial.homogeneousComponent_isHomogeneous N p
  have hfI := hB N hp f hf
  obtain ⟨a, ha, hah⟩ := homogeneous_ideal_bounded_representation H e
    (fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _) f N hf hfI
  let R := ∑ i, a i * P i
  have hRdeg : R.totalDegree ≤ N := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    by_cases hei : e i ≤ N
    · exact (MvPolynomial.totalDegree_mul _ _).trans
        (by have h := (hah i).1.totalDegree_le; dsimp [e] at hei h ⊢; omega)
    · simp [(hah i).2 hei]
  have hRN : MvPolynomial.homogeneousComponent N R = f := by
    dsimp [R]
    rw [map_sum, ← ha]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hei : e i ≤ N
    · rw [mul_comm (a i), homogeneousComponent_mul_homogeneous _ _ _ _ (hah i).1]
      rw [ite_eq_left (Nat.sub_le N (e i)), Nat.sub_sub_self hei]
      exact mul_comm _ _
    · simp [(hah i).2 hei]
  have hremdeg : (p - R).totalDegree ≤ N :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le le_rfl hRdeg)
  have hremN : MvPolynomial.homogeneousComponent N (p - R) = 0 := by
    rw [map_sub, hRN]
    exact sub_self f
  refine ⟨p - R, ?_, ?_⟩
  · have h := totalDegree_strip_top (p - R) N (lt_of_le_of_lt (Nat.zero_le B) hp) hremdeg
    simpa [hremN] using h
  · have hRI : R ∈ Ideal.span (Set.range P) := by
      apply Ideal.sum_mem
      intro i hi
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hRI, sub_zero]

theorem polynomial_top_reduction_bounded_representatives {κ : Type*} [Fintype κ]
    (P : κ → MvPolynomial ι K) (B : ℕ)
    (hB : ∀ n : ℕ, B < n → ∀ p : MvPolynomial ι K, p.IsHomogeneous n →
      p ∈ Ideal.span (Set.range (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) :
    ∀ p : MvPolynomial ι K, ∃ r : MvPolynomial ι K, r.totalDegree ≤ B ∧
      Ideal.Quotient.mk (Ideal.span (Set.range P)) p =
        Ideal.Quotient.mk (Ideal.span (Set.range P)) r := by
  have hrep : ∀ n : ℕ, ∀ p : MvPolynomial ι K, p.totalDegree = n →
      ∃ r : MvPolynomial ι K, r.totalDegree ≤ B ∧
        Ideal.Quotient.mk (Ideal.span (Set.range P)) p =
          Ideal.Quotient.mk (Ideal.span (Set.range P)) r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      by_cases hn : n ≤ B
      · exact ⟨p, hp ▸ hn, rfl⟩
      · obtain ⟨r, hr, he⟩ := polynomial_top_reduction P B hB p
          (by rw [hp]; exact Nat.lt_of_not_ge hn)
        obtain ⟨s, hs, hes⟩ := ih r.totalDegree (hp ▸ hr) r rfl
        exact ⟨s, hs, he.trans hes⟩
  intro p
  exact hrep p.totalDegree p rfl

theorem polynomialQuotient_finite_of_top_zeroLocus [IsAlgClosed K] [Finite ι]
    {κ : Type*} [Fintype κ] (P : κ → MvPolynomial ι K)
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0}) :
    Module.Finite K (MvPolynomial ι K ⧸ Ideal.span (Set.range P)) := by
  classical
  let H := fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)
  let J := Ideal.span (Set.range H)
  have hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K) := by
    apply Ideal.homogeneous_span
    rintro p ⟨i, rfl⟩
    exact ⟨(P i).totalDegree, MvPolynomial.homogeneousComponent_isHomogeneous _ _⟩
  let : Module.Finite K (MvPolynomial ι K ⧸ J) :=
    polynomialQuotient_finite_of_origin_zeroLocus J hz
  obtain ⟨B, hB⟩ := finite_homogeneous_ideal_contains_large_degree J hJ
  have hrep := polynomial_top_reduction_bounded_representatives P B hB
  let I := Ideal.span (Set.range P)
  let pi := Ideal.Quotient.mkₐ K I
  let f : MvPolynomial.restrictTotalDegree ι K B →ₗ[K] (MvPolynomial ι K ⧸ I) :=
    pi.toLinearMap.comp (MvPolynomial.restrictTotalDegree ι K B).subtype
  apply Module.Finite.of_surjective f
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, hr, he⟩ := hrep p
  exact ⟨⟨r, (MvPolynomial.mem_restrictTotalDegree ι B r).mpr hr⟩, he.symm⟩

theorem affine_polynomial_bounded_normal_form [IsAlgClosed K] [CharZero K] {n : ℕ}
    (P : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (he : ∀ i, 0 < (P i).totalDegree)
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial (Fin (n + 1)) K)
      (List.ofFn (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i))))
    (hz : MvPolynomial.zeroLocus K (Ideal.span (Set.range
      (fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)))) = {0}) :
    ∀ f : MvPolynomial (Fin (n + 1)) K, ∃ r : MvPolynomial (Fin (n + 1)) K,
      r.totalDegree ≤ ∑ i, ((P i).totalDegree - 1) ∧
      Ideal.Quotient.mk (Ideal.span (Set.range P)) f =
        Ideal.Quotient.mk (Ideal.span (Set.range P)) r := by
  let H := fun i => MvPolynomial.homogeneousComponent (P i).totalDegree (P i)
  have hB := homogeneous_polynomial_top_degree_bound H (fun i => (P i).totalDegree) he
    (fun i => MvPolynomial.homogeneousComponent_isHomogeneous _ _) hreg hz
  exact polynomial_top_reduction_bounded_representatives P _ hB

end LinearStudy
