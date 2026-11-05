module
public import Linear.GradedIntegerProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]

/-- Integer projections really are pairwise orthogonal projectors,
including all negative degrees. -/
theorem gradedIntegerProjection_projector (i j : ℤ) (x : M) :
    gradedIntegerProjection ℳ i (gradedIntegerProjection ℳ j x) =
      if i = j then gradedIntegerProjection ℳ j x else 0 := by
  by_cases hj : 0 ≤ j
  · have hm : gradedIntegerProjection ℳ j x ∈ ℳ j.toNat := by
      simpa only [gradedIntegerProjection,if_pos hj,gradedModuleProjection_apply] using
        (DirectSum.decompose ℳ x j.toNat).property
    rw [gradedIntegerProjection_on_piece ℳ i j.toNat _ hm]
    have he : i = (j.toNat : ℤ) ↔ i = j := by omega
    simp only [he]
  · have hz : gradedIntegerProjection ℳ j x = 0 := by
      simp only [gradedIntegerProjection,if_neg hj,LinearMap.zero_apply]
    simp only [hz,map_zero,ite_self]

end LinearStudy
