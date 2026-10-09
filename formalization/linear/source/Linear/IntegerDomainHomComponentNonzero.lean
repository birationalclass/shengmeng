module
public import Linear.IntegerDomainHomComponent
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
namespace LinearStudy
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable [AddCommGroup N] [Module K N] [Module A N] [IsScalarTower K A N]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (𝓝 : ℕ → Submodule K N) [DirectSum.Decomposition 𝓝]
variable [SetLike.GradedSMul 𝒜 𝓝]
variable (hgrade : ∀ d : ℕ, ∀ a : A, a ∈ 𝒜 d → ∀ j : ℤ, ∀ x : M,
  x ∈ 𝒟 j → a • x ∈ 𝒟 (j+(d : ℤ)))

theorem integerDomainHomComponent_on_piece (f : M →ₗ[A] N) (k d : ℤ)
    (x : M) (hx : x ∈ 𝒟 d) :
    integerDomainHomComponent 𝒜 𝒟 𝓝 hgrade f k x =
      gradedIntegerProjection 𝓝 (d+k) (f x) :=
  integerDomainHomComponentAux_on_piece 𝒟 𝓝 f k d x hx

/-- The actual component has exactly one degree shift on every
actual homogeneous source element. -/
theorem integerDomainHomComponent_homogeneous (f : M →ₗ[A] N) (k d : ℤ)
    (x : M) (hx : x ∈ 𝒟 d) :
    integerDomainHomComponent 𝒜 𝒟 𝓝 hgrade f k x =
      gradedIntegerProjection 𝓝 (d+k) (integerDomainHomComponent 𝒜 𝒟 𝓝 hgrade f k x) := by
  rw [integerDomainHomComponent_on_piece 𝒜 𝒟 𝓝 hgrade f k d x hx,
    gradedIntegerProjection_projector 𝓝]
  simp

theorem integerDomainHomComponent_exists_nonzero (f : M →ₗ[A] N) (hf : f ≠ 0) :
    ∃ k : ℤ, integerDomainHomComponent 𝒜 𝒟 𝓝 hgrade f k ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ k : ℤ, integerDomainHomComponent 𝒜 𝒟 𝓝 hgrade f k = 0 := by
    simpa only [not_exists,not_not] using h
  apply hf
  ext x
  change f x = 0
  induction x using DirectSum.Decomposition.inductionOn 𝒟 with
  | zero => exact map_zero f
  | @homogeneous n x =>
    have hp (d : ℕ) : gradedModuleProjection 𝓝 d (f x) = 0 := by
      have he := LinearMap.congr_fun (hz ((d : ℤ)-n)) (x : M)
      rw [integerDomainHomComponent_on_piece 𝒜 𝒟 𝓝 hgrade f ((d : ℤ)-n) n
        x x.property] at he
      have hind : n+((d : ℤ)-n) = (d : ℤ) := by omega
      rw [hind] at he
      simpa [gradedIntegerProjection] using he
    rw [← DirectSum.sum_support_decompose 𝓝 (f x)]
    apply Finset.sum_eq_zero
    intro d hd
    exact hp d
  | add x y hx hy => simp [hx,hy]

end LinearStudy
