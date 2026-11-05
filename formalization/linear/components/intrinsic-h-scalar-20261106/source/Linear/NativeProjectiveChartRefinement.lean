module
public import Linear.LocalizedModuleRefinementSemilinear
public import Linear.NativeProjectiveModuleSheaf
public import Linear.HomogeneousLocalizationRefinementValue
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K R M : Type u} [Field K] [CommRing R] [Algebra K R]
variable [AddCommGroup M] [Module R M] [Module K M]
variable (𝒜 : ℕ → Submodule K R) [GradedAlgebra 𝒜]
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar

/-- The actual localized chart element gives a function on its ORIGINAL
basic open, by restriction to each original prime complement. -/
def nativeProjectiveChartRefinement (a : R)
    (x : LocalizedModule (Submonoid.powers a) M)
    (p : ProjectiveSpectrum.basicOpen 𝒜 a) :
    nativeProjectiveModuleAtPrime (D := M) 𝒜 p.1 :=
  originalLocalizedModuleRefinement (Submonoid.powers a)
    p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) x

/-- The original homogeneous chart scalar acts by the ACTUAL structure
sheaf section constructed in mathlib, not an arbitrary scalar action. -/
theorem nativeProjectiveChartRefinement_smul
    (a : R) (c : HomogeneousLocalization.Away 𝒜 a)
    (x : LocalizedModule (Submonoid.powers a) M)
    (p : ProjectiveSpectrum.basicOpen 𝒜 a) :
    nativeProjectiveChartRefinement 𝒜 a (c • x) p =
      ((ProjectiveSpectrum.Proj.awayToSection 𝒜 a).hom c).val p •
        nativeProjectiveChartRefinement 𝒜 a x p := by
  change originalLocalizedModuleRefinement (Submonoid.powers a)
      p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2) (c.val • x) =
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 a).hom c).val p).val •
      nativeProjectiveChartRefinement 𝒜 a x p
  rw [originalLocalizedModuleRefinement_smul]
  have hv := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 a c p
  with_unfolding_all exact (congrArg
    (fun q : Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl =>
      q • nativeProjectiveChartRefinement 𝒜 a x p) hv.symm)
end LinearStudy
