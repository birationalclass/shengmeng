module
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Nilpotent.Basic

/-! Regularity is preserved by nilpotent perturbation of a parameter sequence. Local Noetherian and finite-module hypotheses are explicit. -/
@[expose] public section
namespace LinearStudy
theorem smulRegular_add_nilpotent {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (a n : R)
    (ha : IsSMulRegular M a) (hn : IsNilpotent n) : IsSMulRegular M (a + n) := by
  suffices hzero : ∀ x : M, (a + n) • x = 0 → x = 0 by
    intro x y hxy
    change (a + n) • x = (a + n) • y at hxy
    exact sub_eq_zero.mp (hzero (x - y) (by rw [smul_sub, hxy, sub_self]))
  intro x hx
  have hax : a • x = (-n) • x := by
    rw [add_smul] at hx
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hx
  have hp (k : ℕ) : a ^ k • x = (-n) ^ k • x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_smul, hax, smul_comm, ih, ← mul_smul, ← pow_succ']
  obtain ⟨k, hk⟩ := hn
  have hxk : a ^ k • x = 0 := by
    rw [hp, neg_pow, hk, mul_zero, zero_smul]
  apply IsSMulRegular.pow k ha
  simpa using hxk
open RingTheory.Sequence

theorem regular_cons_replace_nilpotent {R M : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (a b : R) (rs : List R)
    (h : IsRegular M (a :: rs))
    (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R)
    (hb : b ∈ IsLocalRing.maximalIdeal R) (hab : IsNilpotent (b - a)) :
    IsRegular M (b :: rs) := by
  let : Nontrivial M := h.nontrivial
  have hp : (a :: rs).Perm (rs ++ [a]) := by
    simpa using List.perm_append_comm (l₁ := [a]) (l₂ := rs)
  have ht := (IsLocalRing.isRegular_of_perm h hp).toIsWeaklyRegular
  obtain ⟨hr, ha⟩ := (isWeaklyRegular_append_iff M rs [a]).mp ht
  have hba := smulRegular_add_nilpotent a (b - a)
    ((isWeaklyRegular_singleton_iff _ a).mp ha) hab
  have hbb : IsSMulRegular (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) b := by
    simpa only [add_sub_cancel] using hba
  have hw : IsWeaklyRegular M (rs ++ [b]) :=
    (isWeaklyRegular_append_iff M rs [b]).mpr
      ⟨hr, (isWeaklyRegular_singleton_iff _ b).mpr hbb⟩
  have hm : ∀ x ∈ rs ++ [b], x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hmem x hx
    · simpa using (List.mem_singleton.mp hx) ▸ hb
  have hnew := IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M hm hw
  exact IsLocalRing.isRegular_of_perm hnew (List.perm_append_comm (l₁ := rs) (l₂ := [b]))

theorem regular_nilpotent_perturbation {R M : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (rs ts : List R) (h : IsRegular M rs)
    (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R)
    (hmem' : ∀ x ∈ ts, x ∈ IsLocalRing.maximalIdeal R)
    (hdiff : List.Forall₂ (fun a b => IsNilpotent (b - a)) rs ts) : IsRegular M ts := by
  induction hdiff generalizing M with
  | nil => exact h
  | @cons a b rs ts hab hdiff ih =>
    have hb := regular_cons_replace_nilpotent a b rs h
      (fun x hx => hmem x (List.mem_cons_of_mem a hx))
      (hmem' b (List.mem_cons_self)) hab
    obtain ⟨hbreg, htail⟩ := (isRegular_cons_iff M b rs).mp hb
    apply (isRegular_cons_iff M b ts).mpr
    exact ⟨hbreg, ih htail
      (fun x hx => hmem x (List.mem_cons_of_mem a hx))
      (fun x hx => hmem' x (List.mem_cons_of_mem b hx))⟩

end LinearStudy
