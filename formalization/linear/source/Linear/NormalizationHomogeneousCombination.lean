module
public import Linear.NormalizationHomogeneousCoefficientProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K R S ι : Type*} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [SetLike.GradedSMul 𝒜 𝓑] [Fintype ι]

/-- An actual finite expression of a homogeneous source element can use
only the matching homogeneous base coefficients. No coefficient expression
or finite generation is supplied as a replacement for the original source. -/
theorem normalization_homogeneous_combination
    (n : ℕ) (b : S) (hb : b ∈ 𝓑 n)
    (degree : ι → ℕ) (gen : ι → S) (hgen : ∀ i, gen i ∈ 𝓑 (degree i))
    (coefficient : ι → R) (hbound : ∀ i, degree i ≤ n)
    (hexpression : b = ∑ i, coefficient i • gen i) :
    b = ∑ i, gradedModuleProjection 𝒜 (n-degree i) (coefficient i) • gen i := by
  have h := congrArg (gradedModuleProjection 𝓑 n) hexpression
  rw [gradedModuleProjection_on_piece 𝓑 n n b hb, if_pos rfl, map_sum] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [normalizationProjection_smul_source_homogeneous 𝒜 𝓑
    (degree i) n (coefficient i) (gen i) (hgen i), if_pos (hbound i)]

end LinearStudy
