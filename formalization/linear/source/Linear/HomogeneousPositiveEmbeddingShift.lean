module
public import Linear.GradedIntegerProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy
variable {K S M : Type*} [Field K] [CommRing S] [IsDomain S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)

/-- Multiplying an actual homogeneous embedding by a power of an
actual nonzero degree-one element makes its shift a positive integer.
Neither the homogeneous embedding nor the final positive shift is assumed. -/
theorem homogeneous_embedding_exists_positive_shift
    (k : ℤ) (e : M →ₗ[S] S) (he : Function.Injective e)
    (hhom : ∀ d : ℤ, ∀ x : M, x ∈ 𝒟 d →
      e x = gradedIntegerProjection 𝓑 (d+k) (e x))
    (b : S) (hb : b ∈ 𝓑 1) (hne : b ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ g : M →ₗ[S] S, Function.Injective g ∧
      ∀ d : ℤ, ∀ x : M, x ∈ 𝒟 d →
        g x = gradedIntegerProjection 𝓑 (d+(m : ℤ)) (g x) := by
  let N : ℕ := (1-k).toNat
  have hpos : 0 < k+(N : ℤ) := by dsimp [N]; omega
  let m : ℕ := (k+(N : ℤ)).toNat
  have hm : 0 < m := by dsimp [m]; omega
  have hmcast : (m : ℤ) = k+(N : ℤ) := by dsimp [m]; omega
  have hbN : b^N ∈ 𝓑 N := by simpa using SetLike.pow_mem_graded N hb
  let g : M →ₗ[S] S := b^N • e
  have hg : Function.Injective g := by
    intro x y hxy
    apply he
    apply mul_left_cancel₀ (pow_ne_zero N hne)
    exact hxy
  refine ⟨m,hm,g,hg,?_⟩
  intro d x hx
  change b^N • e x = gradedIntegerProjection 𝓑 (d+(m : ℤ)) (b^N • e x)
  rw [gradedIntegerProjection_smul_homogeneous 𝓑 𝓑 N (d+(m : ℤ)) (b^N) hbN (e x)]
  have hind : d+(m : ℤ)-(N : ℤ) = d+k := by omega
  rw [hind,← hhom d x hx]

end LinearStudy
