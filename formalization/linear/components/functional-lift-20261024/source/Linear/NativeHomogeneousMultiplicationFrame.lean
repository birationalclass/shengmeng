module
public import Linear.NativeHomogeneousSectionFrame
public import Linear.NativeIntegerTwistScalarCommute
public import Linear.NativeProjectiveHomogeneousSMul
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The actual degree-zero chart function ell/a^m, restricted to U. -/
def nativeHomogeneousChartCoefficient (m : ℕ) (ell : 𝓑 m)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj (op U) :=
  (((Proj 𝓑).presheaf.map (homOfLE hU).op).hom
    ((Proj.basicOpenIsoAway 𝓑 a ha one_pos).hom.hom
      (HomogeneousLocalization.Away.mk 𝓑 ha m (ell : S)
        (by simpa using ell.property))))

/-- Multiplying the chart coefficient by the actual coordinate frame
recovers the original polynomial at every original prime. -/
theorem nativeHomogeneousChartCoefficient_localizedValue (m : ℕ) (ell : 𝓑 m)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (x : U) :
    ((nativePrimeCoordinateUnit 𝓑 x.1 a (hU x.2) ^ (m : ℤ) :
      (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
        Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) *
      ((nativeHomogeneousChartCoefficient 𝓑 m ell a ha U hU).1 x).val =
    algebraMap S (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) (ell : S) := by
  have h := congrArg (fun s => nativeProjectiveRingModuleLocalizationEquiv 𝓑 x.1 (s.1 x))
    (nativePositiveHomogeneousGlobalSection_frame 𝓑 m ell a ha U hU)
  change nativeProjectiveRingModuleLocalizationEquiv 𝓑 x.1
    ((nativeIntegerTwistSectionFrame 𝓑 a ha (m : ℤ) (op U) (fun p => hU p.2)
      (nativeHomogeneousChartCoefficient 𝓑 m ell a ha U hU)).1 x) =
    nativeProjectiveRingModuleLocalizationEquiv 𝓑 x.1 (LocalizedModule.mk (ell : S) 1) at h
  rw [nativeIntegerTwistSectionFrame_localizedValue,
    nativeProjectiveRingModuleLocalizationEquiv_mk, IsLocalization.mk'_one] at h
  exact h

/-- Actual homogeneous sheaf multiplication has chart coefficient ell/a^m
in every integer twist, on every open inside the coordinate chart. -/
theorem nativeHomogeneousMultiplication_frame (m : ℕ) (ell : 𝓑 m)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (k : ℤ)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj (op U)) :
    (nativeProjectiveHomogeneousSMul 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (ell : S) m ell.property k).val.app (op U)
      (nativeIntegerTwistSectionFrame 𝓑 a ha k (op U) (fun p => hU p.2) r) =
    nativeIntegerTwistSectionFrame 𝓑 a ha (k+(m : ℤ)) (op U) (fun p => hU p.2)
      (nativeHomogeneousChartCoefficient 𝓑 m ell a ha U hU * r) := by
  apply Subtype.ext
  funext x
  apply (nativeProjectiveRingModuleLocalizationEquiv 𝓑 x.1).injective
  rw [nativeProjectiveHomogeneousSMul_section_value, nativeRingLocalization_original_smul,
    nativeIntegerTwistSectionFrame_localizedValue,
    nativeIntegerTwistSectionFrame_localizedValue]
  rw [← nativeHomogeneousChartCoefficient_localizedValue 𝓑 m ell a ha U hU x,
    zpow_add, Units.val_mul]
  change _ = _ * _ * (((nativeHomogeneousChartCoefficient 𝓑 m ell a ha U hU).1 x) *
    (r.1 x)).val
  rw [HomogeneousLocalization.val_mul]
  ring
end LinearStudy
