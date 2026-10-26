module
public import Linear.NativeGradedWeightedCoefficientMap
public import Linear.IntegerGradedSurjectionPreimage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K R M N : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable [AddCommGroup N] [Module R N] [Module K N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable [DirectSum.Decomposition D] [DirectSum.Decomposition E]
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (hE : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : N,x ∈ E j → z • x ∈ E ((n:ℤ)+j))
variable (f : M →ₗ[R] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
include hE
/-- An actual graded surjection is surjective on every actual weighted
chart module. No torsion-freeness, flatness or chart isomorphism is assumed. -/
theorem nativeGradedModuleAwayDegreeZeroCoefficientMap_surjective
    (he : Function.Surjective f) (d : ℕ) (a : R) (ha : a ∈ A d) :
    Function.Surjective (nativeGradedModuleAwayDegreeZeroCoefficientMap A D E hD f hf d a ha) := by
  intro x
  obtain ⟨n,m,hm,hx⟩ := nativeGradedModuleAwayDegreeZero_exists_fraction A E hE d a ha x.val x.property
  obtain ⟨y,hy,hey⟩ := integerDegreeZeroSurjection_homogeneous_preimages D E f hf he _ m hm
  refine ⟨⟨LocalizedModule.mk y (⟨a^n,⟨n,rfl⟩⟩ : Submonoid.powers a),
    Submodule.subset_span ⟨n,y,hy,rfl⟩⟩,?_⟩
  apply Subtype.ext
  change LocalizedModule.map (Submonoid.powers a) f _ = x.val
  rw [LocalizedModule.map_mk,hey]
  exact hx.symm
end LinearStudy
