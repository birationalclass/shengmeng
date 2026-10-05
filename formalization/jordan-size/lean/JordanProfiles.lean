import JordanBounds
import PowerFactors
noncomputable section
namespace JordanSize
variable {K V : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
 [AddCommGroup V] [Module K V] [Module ℚ V] [IsScalarTower ℚ K V]
 [FiniteDimensional K V] {T : Module.End K V}

def largestJordanBlock (T : Module.End K V) : ℕ :=
  sInf {j | JordanBound T j}

def kernelProfile (D : Module.End K V) (j : ℕ) : ℕ :=
  Module.finrank K (LinearMap.ker (D^j))

/-- Kernel growth determines the number of Jordan blocks of each size. -/
def blockMultiplicity (D : Module.End K V) (r : ℕ) : ℕ :=
  (kernelProfile D r - kernelProfile D (r-1)) -
    (kernelProfile D (r+1) - kernelProfile D r)

lemma largestJordanBlock_log (F : Factors T) :
    largestJordanBlock T = nilpotencyClass F.log := by
  unfold largestJordanBlock nilpotencyClass
  congr 1
  ext j
  exact jordanBound_log_iff F j

lemma largestJordanBlock_characterization [Nontrivial V] (F : Factors T) :
    largestJordanBlock T = 1 + (nilpotencyClass F.log - 1) ∧
    F.log^(largestJordanBlock T - 1) ≠ 0 ∧
    F.log^(largestJordanBlock T) = 0 ∧
    (∀ j, largestJordanBlock T ≤ j → F.log^j = 0) := by
  rw [largestJordanBlock_log F]
  refine ⟨by have h := pos_nilpotencyClass_iff.mpr F.log_nilpotent; omega,
    pow_pred_nilpotencyClass F.log_nilpotent, pow_nilpotencyClass F.log_nilpotent, ?_⟩
  intro j hj
  exact pow_eq_zero_of_le hj (pow_nilpotencyClass F.log_nilpotent)

lemma power_kernelProfile (F : Factors T) (a : ℕ) (ha : 0 < a) :
    ∀ j, kernelProfile (F.power a).log j = kernelProfile F.log j := by
  intro j
  unfold kernelProfile
  rw [F.log_power]
  rw [(nonzero_smul_filtrations F.log (a : ℚ) (by exact_mod_cast ha.ne') j).1]

lemma power_blockMultiplicity (F : Factors T) (a : ℕ) (ha : 0 < a) :
    ∀ r, blockMultiplicity (F.power a).log r = blockMultiplicity F.log r := by
  intro r
  simp only [blockMultiplicity, power_kernelProfile F a ha]

lemma power_largestJordanBlock (F : Factors T) (a : ℕ) (ha : 0 < a) :
    largestJordanBlock (T^a) = largestJordanBlock T := by
  rw [largestJordanBlock_log (F.power a), largestJordanBlock_log F, F.log_power]
  unfold nilpotencyClass
  congr 1
  ext j
  exact (nonzero_smul_filtrations F.log (a : ℚ) (by exact_mod_cast ha.ne') j).2.2
end JordanSize
#print axioms JordanSize.largestJordanBlock_characterization
#print axioms JordanSize.power_kernelProfile
#print axioms JordanSize.power_blockMultiplicity
#print axioms JordanSize.power_largestJordanBlock
