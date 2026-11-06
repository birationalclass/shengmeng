module
public import Linear.GradedSubalgebraDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v
variable {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]

/-- The degree-q Veronese subalgebra consists of finite sums of the
original degree-qn pieces. Its operations are inherited from S. -/
def originalDegreeVeroneseAlgebra (q : ℕ) : Subalgebra K S := by
  let P : ℕ → Submodule K S := fun n => B (q * n)
  let V : Submodule K S := ⨆ n, P n
  refine
    { carrier := V
      add_mem' := V.add_mem
      mul_mem' := ?_
      algebraMap_mem' := ?_ }
  · intro x y hx hy
    refine Submodule.iSup_induction P (motive := fun a => a * y ∈ V) hx ?_ ?_ ?_
    · intro i a ha
      refine Submodule.iSup_induction P (motive := fun b => a * b ∈ V) hy ?_ ?_ ?_
      · intro j b hb
        apply Submodule.mem_iSup_of_mem (i+j)
        change a * b ∈ B (q * (i+j))
        rw [Nat.mul_add]
        exact SetLike.mul_mem_graded ha hb
      · simpa only [mul_zero] using V.zero_mem
      · intro b₁ b₂ h₁ h₂
        rw [mul_add]
        exact V.add_mem h₁ h₂
    · simpa only [zero_mul] using V.zero_mem
    · intro a₁ a₂ h₁ h₂
      rw [add_mul]
      exact V.add_mem h₁ h₂
  · intro k
    apply Submodule.mem_iSup_of_mem 0
    change algebraMap K S k ∈ B (q * 0)
    simpa only [Nat.mul_zero, Algebra.smul_def, mul_one] using
      (B 0).smul_mem k (SetLike.one_mem_graded B)

/-- The original degree-qn piece lies in the Veronese subalgebra. -/
theorem originalDegreeVeroneseAlgebra_mem_of_mem
    (q n : ℕ) {x : S} (hx : x ∈ B (q * n)) :
    x ∈ originalDegreeVeroneseAlgebra B q :=
  Submodule.mem_iSup_of_mem n hx

/-- Reindexed degree n, with the exact original degree-qn condition. -/
def originalDegreeVeronesePiece (q n : ℕ) :
    Submodule K (originalDegreeVeroneseAlgebra B q) :=
  (B (q * n)).comap (originalDegreeVeroneseAlgebra B q).val.toLinearMap

theorem originalDegreeVeronesePiece_one_iff (q : ℕ)
    (x : originalDegreeVeroneseAlgebra B q) :
    x ∈ originalDegreeVeronesePiece B q 1 ↔ (x : S) ∈ B q := by
  change ((x : S) ∈ B (q * 1)) ↔ (x : S) ∈ B q
  rw [Nat.mul_one]

end LinearStudy
#check LinearStudy.originalDegreeVeroneseAlgebra
#print axioms LinearStudy.originalDegreeVeroneseAlgebra
#check LinearStudy.originalDegreeVeroneseAlgebra_mem_of_mem
#print axioms LinearStudy.originalDegreeVeroneseAlgebra_mem_of_mem
#check LinearStudy.originalDegreeVeronesePiece
#print axioms LinearStudy.originalDegreeVeronesePiece
#check LinearStudy.originalDegreeVeronesePiece_one_iff
#print axioms LinearStudy.originalDegreeVeronesePiece_one_iff
