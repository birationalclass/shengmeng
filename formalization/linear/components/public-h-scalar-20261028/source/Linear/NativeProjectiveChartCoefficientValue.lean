module
public import Linear.LocalizedModuleRefinementNaturality
public import Linear.NativeProjectiveModuleLocalMap
public import Linear.NativeProjectiveChartRefinement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry
universe u
variable {K R M N : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable [AddCommGroup N] [Module R N] [Module K N]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeProjectiveAtPrimeModuleScalar
/-- ORIGINAL coefficient maps commute with ACTUAL chart refinement at
EACH ORIGINAL source prime,retaining the original localized numerator. -/
theorem nativeProjectiveChartRefinement_coefficient (a : R) (f : M →ₗ[R] N)
    (x : LocalizedModule (Submonoid.powers a) M) (p : ProjectiveSpectrum.basicOpen A a) :
    nativeProjectiveModuleAtPrimeMap A f p.1 (nativeProjectiveChartRefinement A a x p) =
      nativeProjectiveChartRefinement A a (LocalizedModule.map (Submonoid.powers a) f x) p := by
  change LocalizedModule.map p.1.asHomogeneousIdeal.toIdeal.primeCompl f
    (originalLocalizedModuleRefinement (Submonoid.powers a) p.1.asHomogeneousIdeal.toIdeal.primeCompl
      (Submonoid.powers_le.mpr p.2) x) = _
  exact originalLocalizedModuleRefinement_map (Submonoid.powers a)
    p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) f x
end LinearStudy
