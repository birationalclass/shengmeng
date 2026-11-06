module
public import Linear.OriginalDegreeVeroneseAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
universe u v w
variable {K : Type u} {S : Type v} {M : Type w}
variable [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable (D : ℤ → Submodule K M)
variable (hD : ∀ (n : ℕ) (d : ℤ) (c : S), c ∈ B n →
  ∀ x : M, x ∈ D d → c • x ∈ D ((n : ℤ) + d))

/-- The original degree-qn coefficient pieces form a module over the
degree-q Veronese subalgebra. -/
def originalDegreeVeroneseCoefficient (q : ℕ) :
    Submodule (originalDegreeVeroneseAlgebra B q) M := by
  let W : Submodule K M := ⨆ j : ℤ, D ((q : ℤ) * j)
  refine {carrier := W, zero_mem' := W.zero_mem, add_mem' := W.add_mem, smul_mem' := ?_}
  intro c x hx
  have hc : (c : S) ∈ ⨆ n, B (q * n) := c.property
  have hxW : x ∈ W := hx
  change (c : S) • x ∈ W
  refine Submodule.iSup_induction (fun n => B (q * n))
    (motive := fun a => a • x ∈ W) hc ?_ ?_ ?_
  · intro n a ha
    refine Submodule.iSup_induction (fun j : ℤ => D ((q : ℤ) * j))
      (motive := fun y => a • y ∈ W) hxW ?_ ?_ ?_
    · intro j y hy
      apply Submodule.mem_iSup_of_mem ((n : ℤ) + j)
      change a • y ∈ D ((q : ℤ) * ((n : ℤ) + j))
      rw [mul_add, ← Nat.cast_mul]
      exact hD (q * n) ((q : ℤ) * j) a ha y hy
    · simpa only [smul_zero] using W.zero_mem
    · intro y z hy hz
      rw [smul_add]
      exact W.add_mem hy hz
  · simpa only [zero_smul] using W.zero_mem
  · intro a b ha hb
    rw [add_smul]
    exact W.add_mem ha hb

theorem originalDegreeVeroneseCoefficient_mem_of_mem
    (q : ℕ) (j : ℤ) {x : M} (hx : x ∈ D ((q : ℤ) * j)) :
    x ∈ originalDegreeVeroneseCoefficient B D hD q :=
  Submodule.mem_iSup_of_mem j hx

end LinearStudy
#check LinearStudy.originalDegreeVeroneseCoefficient
#print axioms LinearStudy.originalDegreeVeroneseCoefficient
#check LinearStudy.originalDegreeVeroneseCoefficient_mem_of_mem
#print axioms LinearStudy.originalDegreeVeroneseCoefficient_mem_of_mem

