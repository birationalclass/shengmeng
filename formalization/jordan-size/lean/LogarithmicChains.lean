import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Tactic

/-!
The linear part of JS-lemmas, Lemma 1.1.
The filtration argument works over any field. Interpreting the polynomial
as the finite logarithm requires a characteristic-zero coefficient field
and a truncation beyond the nilpotence bound.
Main theorem: `logarithmicChains`.
-/

noncomputable section
open Finset
namespace JordanSize

variable {K V : Type*} [Field K]
  [AddCommGroup V] [Module K V]

/-- A finite polynomial in an endomorphism. -/
def tail (D : Module.End K V) (c : ℕ → K) (m : ℕ) : Module.End K V :=
  ∑ j ∈ range m, c j • D ^ j

lemma commute_tail (D : Module.End K V) (c : ℕ → K) (m : ℕ) :
    Commute D (tail D c m) := by
  apply Commute.sum_right
  intro j _
  exact (Commute.refl D).pow_right j |>.smul_right (c j)

/-- A commuting invertible factor does not change any kernel or image filtration. -/
lemma unit_factor_filtrations (D Q : Module.End K V)
    (hcomm : Commute D Q) (hunit : IsUnit Q) (j : ℕ) :
    LinearMap.ker ((D * Q) ^ j) = LinearMap.ker (D ^ j) ∧
    LinearMap.range ((D * Q) ^ j) = LinearMap.range (D ^ j) ∧
    ((D * Q) ^ j = 0 ↔ D ^ j = 0) := by
  have hb := (Module.End.isUnit_iff (Q ^ j)).mp (hunit.pow j)
  have hp := hcomm.mul_pow j
  have hc : D ^ j * Q ^ j = Q ^ j * D ^ j :=
    (hcomm.pow_pow j j).eq
  constructor
  · ext x
    simp only [LinearMap.mem_ker, hp, hc, Module.End.mul_apply]
    exact ⟨fun h => hb.1 (by simpa using h), fun h => by simp [h]⟩
  constructor
  · ext x
    simp only [LinearMap.mem_range, hp, Module.End.mul_apply]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨(Q ^ j) y, hy⟩
    · rintro ⟨y, hy⟩
      obtain ⟨z, hz⟩ := hb.2 y
      exact ⟨z, by simpa [hz] using hy⟩
  · rw [hp]
    constructor
    · intro h
      exact (hunit.pow j).mul_right_cancel (by simpa using h)
    · intro h
      simp [h]

lemma unit_one_add_tail (D : Module.End K V) (hD : IsNilpotent D)
    (c : ℕ → K) (m : ℕ) : IsUnit (1 + D * tail D c m) := by
  exact ((commute_tail D c m).isNilpotent_mul_right hD).isUnit_one_add

/-- Truncated logarithm polynomial. It is the actual finite logarithm when
the coefficient field has characteristic zero and `D^(m+2)=0`. -/
def logFinite (D : Module.End K V) (m : ℕ) : Module.End K V :=
  D * (1 + D * tail D (fun j => (-1 : K) ^ (j + 1) / (j + 2)) m)

/-- Explicit finite expansion; the leading coefficient is exactly one. -/
lemma logFinite_expansion (D : Module.End K V) (m : ℕ) :
    logFinite D m = D +
      ∑ j ∈ range m, ((-1 : K) ^ (j + 1) / (j + 2)) • D ^ (j + 2) := by
  unfold logFinite tail
  rw [mul_add, mul_one, ← mul_assoc, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [mul_smul_comm, ← pow_two, ← pow_add, Nat.add_comm 2 j]

/-- Formal Jordan-filtration statement of the logarithmic part of Lemma 1.1.
All exponents are included, not just the nilpotency index. -/
theorem logarithmicChains (D : Module.End K V) (hD : IsNilpotent D) (m : ℕ) :
    IsNilpotent (logFinite D m) ∧
    (∀ j : ℕ,
      LinearMap.ker ((logFinite D m) ^ j) = LinearMap.ker (D ^ j) ∧
      LinearMap.range ((logFinite D m) ^ j) = LinearMap.range (D ^ j) ∧
      ((logFinite D m) ^ j = 0 ↔ D ^ j = 0)) ∧
    nilpotencyClass (logFinite D m) = nilpotencyClass D := by
  let Q := 1 + D * tail D (fun j => (-1 : K) ^ (j + 1) / (j + 2)) m
  have hc : Commute D Q :=
    (Commute.one_right D).add_right ((Commute.refl D).mul_right (commute_tail D _ m))
  have hq : IsUnit Q := unit_one_add_tail D hD _ m
  have hfil (j : ℕ) := unit_factor_filtrations D Q hc hq j
  have heq : logFinite D m = D * Q := rfl
  have hn : IsNilpotent (logFinite D m) := by
    obtain ⟨r, hr⟩ := hD
    exact ⟨r, (heq ▸ (hfil r).2.2).mpr hr⟩
  refine ⟨hn, ?_, ?_⟩
  · intro j
    simpa only [heq] using hfil j
  · unfold nilpotencyClass
    congr 1
    ext j
    exact (heq ▸ (hfil j).2.2)

end JordanSize

#print axioms JordanSize.logarithmicChains
