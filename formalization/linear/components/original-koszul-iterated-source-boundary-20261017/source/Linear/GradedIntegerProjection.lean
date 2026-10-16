module
public import Linear.GradedModuleProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable [SetLike.GradedSMul 𝒜 ℳ]

/-- Actual homogeneous projection extended to integer degrees by zero
below degree zero. Negative Hom degrees are not truncated to degree zero. -/
def gradedIntegerProjection (i : ℤ) : M →ₗ[K] M :=
  if 0 ≤ i then gradedModuleProjection ℳ i.toNat else 0

theorem gradedIntegerProjection_on_piece (i : ℤ) (n : ℕ) (m : M)
    (hm : m ∈ ℳ n) :
    gradedIntegerProjection ℳ i m = if i = (n : ℤ) then m else 0 := by
  unfold gradedIntegerProjection
  by_cases hi : 0 ≤ i
  · rw [if_pos hi, gradedModuleProjection_on_piece ℳ i.toNat n m hm]
    have he : i.toNat = n ↔ i = (n : ℤ) := by omega
    simp only [he]
  · rw [if_neg hi]
    have he : i ≠ (n : ℤ) := by omega
    simp [he]

/-- Integer homogeneous projections commute with multiplication by
an actual homogeneous scalar, with the exact degree shift. -/
theorem gradedIntegerProjection_smul_homogeneous (d : ℕ) (i : ℤ)
    (a : A) (ha : a ∈ 𝒜 d) (m : M) :
    gradedIntegerProjection ℳ i (a • m) =
      a • gradedIntegerProjection ℳ (i - (d : ℤ)) m := by
  unfold gradedIntegerProjection
  by_cases hi : 0 ≤ i
  · rw [if_pos hi, gradedModuleProjection_smul_homogeneous 𝒜 ℳ d i.toNat a ha m]
    by_cases hd : d ≤ i.toNat
    · have hi' : 0 ≤ i - (d : ℤ) := by omega
      have hsub : (i - (d : ℤ)).toNat = i.toNat - d := by omega
      rw [if_pos hd, if_pos hi', hsub]
    · have hi' : ¬ 0 ≤ i - (d : ℤ) := by omega
      simp only [if_neg hd, if_neg hi', LinearMap.zero_apply, smul_zero]
  · have hi' : ¬ 0 ≤ i - (d : ℤ) := by omega
    simp only [if_neg hi, if_neg hi', LinearMap.zero_apply, smul_zero]

end LinearStudy
