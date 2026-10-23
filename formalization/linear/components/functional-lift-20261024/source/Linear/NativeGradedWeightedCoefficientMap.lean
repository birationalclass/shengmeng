module
public import Linear.NativeGradedWeightedSingleFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
variable {K R M N : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable [AddCommGroup N] [Module R N] [Module K N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (D : ℤ → Submodule K M) (E : ℤ → Submodule K N)
variable (hD : ∀ n : ℕ,∀ j : ℤ,∀ z : R,z ∈ A n → ∀ x : M,x ∈ D j → z • x ∈ D ((n:ℤ)+j))
variable (f : M →ₗ[R] N) (hf : ∀ j : ℤ,∀ x : M,x ∈ D j → f x ∈ E j)
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
include hD hf
/-- An ORIGINAL degree-zero coefficient map preserves the ACTUAL weighted
zero chart. Numerator degree is n*d for the TRUE denominator degree d. -/
theorem nativeGradedModuleAwayDegreeZero_coefficient_mem (d : ℕ) (a : R) (ha : a ∈ A d)
    (x : LocalizedModule (Submonoid.powers a) M)
    (hx : x ∈ nativeGradedModuleAwayDegreeZero A D d a) :
    LocalizedModule.map (Submonoid.powers a) f x ∈ nativeGradedModuleAwayDegreeZero A E d a := by
  obtain ⟨n,m,hm,rfl⟩ := nativeGradedModuleAwayDegreeZero_exists_fraction A D hD d a ha x hx
  rw [LocalizedModule.map_mk]
  exact Submodule.subset_span ⟨n,f m,hf _ m hm,rfl⟩
/-- The ORIGINAL localized coefficient function on the SAME weighted chart.
No replacement coefficient map or chart scalar action is introduced. -/
def nativeGradedModuleAwayDegreeZeroCoefficientMap (d : ℕ) (a : R) (ha : a ∈ A d)
    (x : nativeGradedModuleAwayDegreeZero A D d a) : nativeGradedModuleAwayDegreeZero A E d a :=
  ⟨LocalizedModule.map (Submonoid.powers a) f x.val,
    nativeGradedModuleAwayDegreeZero_coefficient_mem A D E hD f hf d a ha x.val x.property⟩
end LinearStudy
