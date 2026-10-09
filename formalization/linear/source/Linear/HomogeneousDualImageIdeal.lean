module
public import Linear.IntegerGradedModuleProjection
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K S D : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module K D] [Module S D] [IsScalarTower K S D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) [DirectSum.Decomposition 𝒟]

/-- The actual range of a homogeneous map from an integer-graded
module is an actual homogeneous ideal of the target coordinate ring. -/
def homogeneousDualImageIdeal (k : ℤ) (e : D →ₗ[S] S)
    (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d →
      e x = gradedIntegerProjection 𝓑 (d+k) (e x)) : HomogeneousIdeal 𝓑 where
  toSubmodule := LinearMap.range e
  is_homogeneous' := by
    intro i y hy
    obtain ⟨x,rfl⟩ := hy
    refine ⟨integerGradedModuleProjection 𝒟 ((i : ℤ)-k) x,?_⟩
    exact integerHomogeneousMap_projection 𝓑 𝒟 k e hh i x

/-- Compare the actual source with its constructed image ideal using
the actual homogeneous injection, instead of supplying an image model. -/
def homogeneousDualImageEquiv (k : ℤ) (e : D →ₗ[S] S)
    (he : Function.Injective e)
    (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d →
      e x = gradedIntegerProjection 𝓑 (d+k) (e x)) :
    D ≃ₗ[S] (homogeneousDualImageIdeal 𝓑 𝒟 k e hh).toIdeal :=
  LinearEquiv.ofInjective e he

theorem homogeneousDualImageEquiv_projection (k : ℤ) (e : D →ₗ[S] S)
    (he : Function.Injective e)
    (hh : ∀ d : ℤ, ∀ x : D, x ∈ 𝒟 d →
      e x = gradedIntegerProjection 𝓑 (d+k) (e x))
    (i : ℕ) (x : D) :
    (homogeneousDualImageEquiv 𝓑 𝒟 k e he hh
      (integerGradedModuleProjection 𝒟 ((i : ℤ)-k) x) : S) =
      gradedModuleProjection 𝓑 i (homogeneousDualImageEquiv 𝓑 𝒟 k e he hh x : S) :=
  integerHomogeneousMap_projection 𝓑 𝒟 k e hh i x

end LinearStudy
