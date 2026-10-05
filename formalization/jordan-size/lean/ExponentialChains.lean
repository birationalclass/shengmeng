import OperatorLog
import LogarithmicChains

noncomputable section
namespace JordanSize
open Finset
variable {A : Type*} [Ring A] [Algebra ℚ A]

def expQuotient (D : A) (m : ℕ) : A :=
  1 + D * ∑ j ∈ range m, ((j+2).factorial : ℚ)⁻¹ • D^j

lemma expQuotient_commute (D : A) (m : ℕ) : Commute D (expQuotient D m) := by
  apply (Commute.one_right D).add_right
  apply (Commute.refl D).mul_right
  apply Commute.sum_right
  intro j hj
  exact ((Commute.refl D).pow_right j).smul_right _

lemma expQuotient_unit (D : A) (hD : IsNilpotent D) (m : ℕ) :
    IsUnit (expQuotient D m) := by
  apply IsNilpotent.isUnit_one_add
  apply Commute.isNilpotent_mul_right _ hD
  apply Commute.sum_right
  intro j hj
  exact ((Commute.refl D).pow_right j).smul_right _

lemma exp_sub_one_factor (D : A) (m : ℕ) (hk : D^(m+2) = 0) :
    IsNilpotent.exp D - 1 = D * expQuotient D m := by
  rw [IsNilpotent.exp_eq_sum hk]
  have hsum : (∑ i ∈ range (m+2), (i.factorial : ℚ)⁻¹ • D^i) =
      1 + D + ∑ j ∈ range m, ((j+2).factorial : ℚ)⁻¹ • D^(j+2) := by
    rw [show m+2=(m+1)+1 by omega, sum_range_succ', sum_range_succ']
    simp [add_assoc, add_comm, add_left_comm]
  rw [hsum]
  unfold expQuotient
  rw [mul_add, mul_one, ← mul_assoc, mul_sum]
  have he : (∑ j ∈ range m, D * D * (((j+2).factorial : ℚ)⁻¹ • D^j)) =
      ∑ j ∈ range m, ((j+2).factorial : ℚ)⁻¹ • D^(j+2) := by
    apply sum_congr rfl
    intro j hj
    rw [mul_smul_comm, ← pow_two, ← pow_add, Nat.add_comm 2 j]
  rw [he]
  abel

variable {K V : Type*} [Field K] [Algebra ℚ K]
  [AddCommGroup V] [Module K V] [Module ℚ V] [IsScalarTower ℚ K V]

/-- The finite exponential and its logarithm have identical Jordan filtrations. -/
theorem exponentialChains (D : Module.End K V) (hD : IsNilpotent D) :
    ∀ j : ℕ,
      LinearMap.ker ((IsNilpotent.exp D - 1)^j) = LinearMap.ker (D^j) ∧
      LinearMap.range ((IsNilpotent.exp D - 1)^j) = LinearMap.range (D^j) ∧
      ((IsNilpotent.exp D - 1)^j = 0 ↔ D^j = 0) := by
  obtain ⟨m, hm⟩ := hD
  have hm' : D^(m+2) = 0 := pow_eq_zero_of_le (by omega) hm
  intro j
  rw [exp_sub_one_factor D m hm']
  exact unit_factor_filtrations D (expQuotient D m)
    (expQuotient_commute D m) (expQuotient_unit D ⟨m, hm⟩ m) j

theorem exponential_nilpotencyClass (D : Module.End K V) (hD : IsNilpotent D) :
    nilpotencyClass (IsNilpotent.exp D - 1) = nilpotencyClass D := by
  unfold nilpotencyClass
  congr 1
  ext j
  exact (exponentialChains D hD j).2.2

end JordanSize
#print axioms JordanSize.exponentialChains
#print axioms JordanSize.exponential_nilpotencyClass
