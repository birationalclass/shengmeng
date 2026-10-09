module
public import Linear.NativeProjectiveModuleSheafEpi
public import Linear.IntegerGradedSurjectionPreimage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D E : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D) (ℰ : ℤ → Submodule K E)
variable [DirectSum.Decomposition 𝒟] [DirectSum.Decomposition ℰ]
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))
variable (hE : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : E, ell ∈ ℰ d → b • ell ∈ ℰ ((n : ℤ)+d))

/-- The actual native associated-module construction sends an ordinary
surjective degree-zero homogeneous module map to a genuine sheaf epi.
Homogeneous preimages are proved by projection, not supplied as data. -/
theorem nativeProjectiveHomogeneousSurjectionSheaf_epi
    (e : D →ₗ[S] E)
    (hh : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ (d+0))
    (he : Function.Surjective e) (k : ℤ) :
    Epi (nativeProjectiveModuleSheafMap 𝓑 𝒟 ℰ hD hE 0 e hh k) := by
  have hhom : ∀ d : ℤ, ∀ ell : D, ell ∈ 𝒟 d → e ell ∈ ℰ d := by
    simpa only [add_zero] using hh
  exact nativeProjectiveModuleSheafMap_epi 𝓑 𝒟 ℰ hD hE e hh
    (integerDegreeZeroSurjection_homogeneous_preimages 𝒟 ℰ e hhom he) k

end LinearStudy
