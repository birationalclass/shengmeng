module
public import Linear.NativeHomogeneousIntegerFrameMultiply
public import Mathlib.Geometry.RingedSpace.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The SAME actual original coefficient H/a^q is a unit on every open
contained in BOTH original D_+(a) and D_+(H). No stalk-unit or inverse
certificate is assumed: the original numerator is inverted at each prime. -/
theorem nativeHomogeneousChartCoefficientSection_isUnit (q : ℕ) (ell : 𝓑 q)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (hH : U ≤ Proj.basicOpen 𝓑 (ell:S)) :
    IsUnit (nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU) := by
  apply (Proj 𝓑).toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  apply (isUnit_map_iff (Proj.stalkIso' 𝓑 x) _).mp
  erw [Proj.stalkIso'_germ]
  apply (HomogeneousLocalization.isUnit_iff_isUnit_val 𝓑 x.asHomogeneousIdeal.toIdeal _).mp
  have hh : IsUnit (algebraMap S
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) (ell:S)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr (hH hx)
  have hv := nativeHomogeneousChartCoefficientSection_spec 𝓑 q ell a ha U hU ⟨x,hx⟩
  rw [← hv] at hh
  exact isUnit_of_mul_isUnit_right hh

end LinearStudy