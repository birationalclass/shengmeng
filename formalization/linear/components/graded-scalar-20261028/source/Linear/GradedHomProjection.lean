module
public import Linear.GradedHomPiece
public import Linear.GradedHomFiniteSupport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝓝]

def gradedHomProjection (k : ℤ) : (M →ₗ[A] N) →ₗ[K] (M →ₗ[A] N) where
  toFun f := gradedHomComponent 𝒜 ℳ 𝓝 f k
  map_add' := by
    intro f g
    ext x
    change gradedHomComponent 𝒜 ℳ 𝓝 (f+g) k x =
      gradedHomComponent 𝒜 ℳ 𝓝 f k x+gradedHomComponent 𝒜 ℳ 𝓝 g k x
    induction x using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous d x =>
      rw [gradedHomComponent_on_piece 𝒜 ℳ 𝓝 (f+g) k d x x.property,
        gradedHomComponent_on_piece 𝒜 ℳ 𝓝 f k d x x.property,
        gradedHomComponent_on_piece 𝒜 ℳ 𝓝 g k d x x.property]
      exact map_add (gradedIntegerProjection 𝓝 ((d : ℤ)+k)) (f x) (g x)
    | add x y hx hy => simp only [map_add,hx,hy]; abel
  map_smul' := by
    intro c f
    ext x
    change gradedHomComponent 𝒜 ℳ 𝓝 (c • f) k x =
      c • gradedHomComponent 𝒜 ℳ 𝓝 f k x
    induction x using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous d x =>
      rw [gradedHomComponent_on_piece 𝒜 ℳ 𝓝 (c • f) k d x x.property,
        gradedHomComponent_on_piece 𝒜 ℳ 𝓝 f k d x x.property]
      exact map_smul (gradedIntegerProjection 𝓝 ((d : ℤ)+k)) c (f x)
    | add x y hx hy => simp only [map_add,hx,hy,smul_add]

theorem gradedHomProjection_joint_injective (f g : M →ₗ[A] N)
    (h : ∀ k : ℤ, gradedHomProjection 𝒜 ℳ 𝓝 k f = gradedHomProjection 𝒜 ℳ 𝓝 k g) :
    f = g := by
  by_contra he
  obtain ⟨k,hk⟩ := gradedHomComponent_exists_nonzero 𝒜 ℳ 𝓝 (f-g) (sub_ne_zero.mpr he)
  apply hk
  change gradedHomProjection 𝒜 ℳ 𝓝 k (f-g) = 0
  rw [map_sub,h k,sub_self]

/-- The original map is the finite sum of its actual integer-degree
components, establishing totality of the constructed graded Hom. -/
theorem gradedHomProjection_exists_sum [Module.Finite A M] (f : M →ₗ[A] N) :
    ∃ s : Finset ℤ, (∑ k ∈ s, gradedHomProjection 𝒜 ℳ 𝓝 k f) = f := by
  classical
  obtain ⟨s,hs⟩ := gradedHomComponent_finite_support 𝒜 ℳ 𝓝 f
  refine ⟨s,gradedHomProjection_joint_injective 𝒜 ℳ 𝓝 _ _ ?_⟩
  intro j
  rw [map_sum]
  have hp (k : ℤ) : gradedHomProjection 𝒜 ℳ 𝓝 j (gradedHomProjection 𝒜 ℳ 𝓝 k f) =
      if j = k then gradedHomProjection 𝒜 ℳ 𝓝 k f else 0 :=
    gradedHomComponent_on_homogeneous_map 𝒜 ℳ 𝓝 j k _
      (gradedHomComponent_mem_piece 𝒜 ℳ 𝓝 f k)
  simp_rw [hp]
  by_cases hj : j ∈ s
  · simp [hj]
  · rw [Finset.sum_eq_zero]
    · exact (hs j hj).symm
    · intro k hk
      have hne : j ≠ k := fun h => hj (h ▸ hk)
      simp [hne]

end LinearStudy
