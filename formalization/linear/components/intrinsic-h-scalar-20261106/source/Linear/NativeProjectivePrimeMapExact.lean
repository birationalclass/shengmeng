module
public import Linear.NativeProjectiveModuleLocalMap
public import Mathlib.Algebra.Module.LocalizedModule.Exact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry
universe u
variable {K S D E F : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable [AddCommGroup E] [Module S E] [Module K E]
variable [AddCommGroup F] [Module S F] [Module K F]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Actual projective-prime localization preserves exactness of the
original module maps, with the original native degree-zero scalar action. -/
theorem nativeProjectiveModuleAtPrimeMap_exact
    (a : D →ₗ[S] E) (b : E →ₗ[S] F) (hex : Function.Exact a b)
    (p : ProjectiveSpectrum 𝓑) :
    Function.Exact (nativeProjectiveModuleAtPrimeMap 𝓑 a p)
      (nativeProjectiveModuleAtPrimeMap 𝓑 b p) := by
  exact LocalizedModule.map_exact p.asHomogeneousIdeal.toIdeal.primeCompl a b hex

end LinearStudy
