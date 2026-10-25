module
public import Linear.KoszulFunctionResolution
public import Linear.AffineFiltered
public import Mathlib.Tactic
/-! Actual regular Koszul first-syzygy generation and homogeneous weighted coefficient control. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory RingTheory.Sequence
namespace LinearStudy
variable {R : Type*} [CommRing R] {n : ℕ}

theorem regular_koszul_first_relation
    (H : Fin n → R) (hreg : IsRegular R (List.ofFn H))
    (a : Fin n → R) (ha : ∑ i, a i * H i = 0) :
    ∃ z : ⋀[R]^2 (Fin n → R),
      exteriorPower.oneEquiv R _ (koszulComplex.d (Fintype.linearCombination R H) 1 z) = a := by
  classical
  have he := koszulComplex.exactAt_of_isRegular (List.ofFn H) hreg 1 (by decide)
  rw [koszul_ofFn, HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at he
  let v := (exteriorPower.oneEquiv R (Fin n → R)).symm a
  have hv : koszulComplex.d (Fintype.linearCombination R H) 0 v = 0 := by
    apply (exteriorPower.zeroEquiv R _).injective
    have hh := LinearMap.congr_fun
      (koszulComplex.equiv_comp_koszulComplex.d_zero_eq (Fintype.linearCombination R H)) v
    rw [map_zero]
    change (exteriorPower.zeroEquiv R _) ((koszulComplex.d (Fintype.linearCombination R H) 0) v) =
      (Fintype.linearCombination R H) ((exteriorPower.oneEquiv R _) v) at hh
    rw [hh]
    simpa [v, Fintype.linearCombination_apply, smul_eq_mul] using ha
  obtain ⟨z, hz⟩ := he v hv
  refine ⟨z, ?_⟩
  change koszulComplex.d (Fintype.linearCombination R H) 1 z = v at hz
  rw [hz]
  exact LinearEquiv.apply_symm_apply _ _

theorem koszul_first_differential_wedge (H : Fin n → R) (v : Fin 2 → (Fin n → R)) :
    exteriorPower.oneEquiv R _ (koszulComplex.d (Fintype.linearCombination R H) 1
      (exteriorPower.ιMulti R 2 v)) =
      (Fintype.linearCombination R H (v 0)) • v 1 -
        (Fintype.linearCombination R H (v 1)) • v 0 := by
  simp [koszulComplex.d, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    koszulComplex.dAlternating_apply, Fin.sum_univ_two, Fin.removeNth_apply,
    Fin.tail, sub_eq_add_neg]

theorem koszul_first_differential_skew (H : Fin n → R) (z : ⋀[R]^2 (Fin n → R)) :
    ∃ c : Fin n → Fin n → R, (∀ i j, c i j = -c j i) ∧ (∀ i, c i i = 0) ∧
      ∀ i, (exteriorPower.oneEquiv R _ (koszulComplex.d (Fintype.linearCombination R H) 1 z)) i =
        ∑ j, c i j * H j := by
  classical
  have hz : z ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨fun i j => v 0 j * v 1 i - v 1 j * v 0 i, ?_, ?_, ?_⟩
    · intro i j; ring
    · intro i; ring
    · intro i
      rw [koszul_first_differential_wedge]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fintype.linearCombination_apply,
        Finset.sum_mul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
  | zero =>
    refine ⟨0, by simp, by simp, ?_⟩
    simp
  | add x y hx hy ihx ihy =>
    obtain ⟨cx, hsx, hdx, hex⟩ := ihx
    obtain ⟨cy, hsy, hdy, hey⟩ := ihy
    refine ⟨fun i j => cx i j + cy i j, ?_, ?_, ?_⟩
    · intro i j; dsimp only; rw [hsx i j, hsy i j]; ring
    · intro i; dsimp only; rw [hdx i, hdy i]; simp
    · intro i
      simp only [map_add, Pi.add_apply, hex i, hey i, add_mul, Finset.sum_add_distrib]
  | smul r x hx ih =>
    obtain ⟨c, hs, hd, he⟩ := ih
    refine ⟨fun i j => r * c i j, ?_, ?_, ?_⟩
    · intro i j; dsimp only; rw [hs i j]; ring
    · intro i; dsimp only; rw [hd i]; simp
    · intro i
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, he i, Finset.mul_sum, mul_assoc]

theorem regular_first_syzygy_skew (H : Fin n → R) (hreg : IsRegular R (List.ofFn H))
    (a : Fin n → R) (ha : ∑ i, a i * H i = 0) :
    ∃ c : Fin n → Fin n → R, (∀ i j, c i j = -c j i) ∧ (∀ i, c i i = 0) ∧
      ∀ i, a i = ∑ j, c i j * H j := by
  obtain ⟨z, hz⟩ := regular_koszul_first_relation H hreg a ha
  obtain ⟨c, hs, hd, he⟩ := koszul_first_differential_skew H z
  exact ⟨c, hs, hd, by simpa only [hz] using he⟩

theorem homogeneous_first_syzygy_skew {K ι : Type*} [Field K]
    (H : Fin n → MvPolynomial ι K) (e : Fin n → ℕ)
    (hH : ∀ i, (H i).IsHomogeneous (e i))
    (hreg : IsRegular (MvPolynomial ι K) (List.ofFn H))
    (a : Fin n → MvPolynomial ι K) (N : ℕ)
    (hah : ∀ i, (a i).IsHomogeneous (N - e i))
    (ha0 : ∀ i, ¬e i ≤ N → a i = 0)
    (ha : ∑ i, a i * H i = 0) :
    ∃ c : Fin n → Fin n → MvPolynomial ι K,
      (∀ i j, c i j = -c j i) ∧ (∀ i, c i i = 0) ∧
      (∀ i j, (c i j).IsHomogeneous (N - e i - e j) ∧
        (¬e i + e j ≤ N → c i j = 0)) ∧
      ∀ i, a i = ∑ j, c i j * H j := by
  classical
  obtain ⟨c, hs, hd, hc⟩ := regular_first_syzygy_skew H hreg a ha
  let b := fun i j => if e i + e j ≤ N then
    MvPolynomial.homogeneousComponent (N - e i - e j) (c i j) else 0
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro i j
    dsimp [b]
    rw [Nat.add_comm (e j) (e i), Nat.sub_sub, Nat.sub_sub, Nat.add_comm (e j) (e i)]
    split_ifs
    · rw [hs i j, map_neg]
    · simp
  · intro i
    dsimp [b]
    rw [hd i]
    simp
  · intro i j
    dsimp [b]
    split_ifs with h
    · exact ⟨MvPolynomial.homogeneousComponent_isHomogeneous _ _, fun hn => (hn h).elim⟩
    · exact ⟨MvPolynomial.isHomogeneous_zero ι K _, fun _ => rfl⟩
  · intro i
    by_cases hei : e i ≤ N
    · have hh := congrArg (MvPolynomial.homogeneousComponent (N - e i)) (hc i)
      rw [map_sum, MvPolynomial.homogeneousComponent_eq_self (hah i)] at hh
      rw [hh]
      apply Finset.sum_congr rfl
      intro j hj
      rw [homogeneousComponent_mul_homogeneous _ _ _ _ (hH j)]
      dsimp [b]
      by_cases hij : e i + e j ≤ N
      · rw [ite_eq_left hij, ite_eq_left (by omega)]
      · rw [ite_eq_right hij, ite_eq_right (by omega), zero_mul]
    · rw [ha0 i hei]
      have hfalse : ∀ j, ¬e i + e j ≤ N := by intro j; omega
      simp [b, hfalse]
end LinearStudy
