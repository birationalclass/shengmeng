module
public import Linear.GradedHomComponent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝓝]

theorem gradedHomComponent_on_piece (f : M →ₗ[A] N) (k : ℤ)
    (d : ℕ) (x : M) (hx : x ∈ ℳ d) :
    gradedHomComponent 𝒜 ℳ 𝓝 f k x =
      gradedIntegerProjection 𝓝 ((d : ℤ)+k) (f x) :=
  gradedHomComponentAux_on_piece ℳ 𝓝 f k d x hx

/-- A nonzero actual map has a nonzero homogeneous map component.
The component is constructed from projections, not supplied as an input. -/
theorem gradedHomComponent_exists_nonzero (f : M →ₗ[A] N) (hf : f ≠ 0) :
    ∃ k : ℤ, gradedHomComponent 𝒜 ℳ 𝓝 f k ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ k : ℤ, gradedHomComponent 𝒜 ℳ 𝓝 f k = 0 := by
    simpa only [not_exists,not_not] using h
  apply hf
  ext x
  change f x = 0
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => exact map_zero f
  | @homogeneous n x =>
    have hp (d : ℕ) : gradedModuleProjection 𝓝 d (f x) = 0 := by
      have he := LinearMap.congr_fun (hz ((d : ℤ)-(n : ℤ))) (x : M)
      rw [gradedHomComponent_on_piece 𝒜 ℳ 𝓝 f ((d : ℤ)-(n : ℤ)) n
        (x : M) x.property] at he
      have hind : (n : ℤ)+((d : ℤ)-(n : ℤ)) = (d : ℤ) := by omega
      rw [hind] at he
      simpa [gradedIntegerProjection] using he
    rw [← DirectSum.sum_support_decompose 𝓝 (f x)]
    apply Finset.sum_eq_zero
    intro d hd
    exact hp d
  | add x y hx hy => simp [hx,hy]

end LinearStudy
