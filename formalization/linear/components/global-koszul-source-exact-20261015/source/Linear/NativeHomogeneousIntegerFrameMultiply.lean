module
public import Linear.NativeHomogeneousSectionFrame
public import Linear.NativeProjectiveHomogeneousSMul
public import Linear.NativeIntegerTwistScalarCommute
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- ORIGINAL homogeneous h divided by the ORIGINAL chart coordinate a^q,
as an ACTUAL structure-ring section on any open of the a-chart. -/
def nativeHomogeneousChartCoefficientSection (q : ℕ) (ell : 𝓑 q)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) : (Proj 𝓑).presheaf.obj (op U) :=
  (((Proj 𝓑).presheaf.map (homOfLE hU).op).hom
    ((Proj.basicOpenIsoAway 𝓑 a ha one_pos).hom.hom
      (HomogeneousLocalization.Away.mk 𝓑 ha q (ell : S)
        (by simpa using ell.property))))

/-- The ACTUAL chart coefficient satisfies a^q*(h/a^q)=h at every
original homogeneous prime,from the already proved original section frame. -/
theorem nativeHomogeneousChartCoefficientSection_spec (q : ℕ) (ell : 𝓑 q)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (p : U) :
    ((nativePrimeCoordinateUnit 𝓑 p.1 a (hU p.2) ^ (q:ℤ) :
      (Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl)ˣ) :
        Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) *
      ((nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU).1 p).val =
        algebraMap S (Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) (ell:S) := by
  have hc := congrArg (fun s => nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (s.1 p))
    (nativePositiveHomogeneousGlobalSection_frame 𝓑 q ell a ha U hU)
  change nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1
      ((nativeIntegerTwistSectionFrame 𝓑 a ha (q:ℤ) (op U) (fun p => hU p.2)
        (nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU)).1 p) =
      nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1 (LocalizedModule.mk (ell:S) 1) at hc
  rw [nativeIntegerTwistSectionFrame_localizedValue,
    nativeProjectiveRingModuleLocalizationEquiv_mk, IsLocalization.mk'_one] at hc
  exact hc

/-- Multiplication by ORIGINAL h between arbitrary INTEGER twists becomes
multiplication by the SAME ACTUAL dehomogenized h/a^q in original a-frames.
This is an equality of the ORIGINAL section maps,for all integer k. -/
theorem nativeIntegerTwistSectionFrame_homogeneous_multiply (q : ℕ) (ell : 𝓑 q)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (k : ℤ)
    (r : (Proj 𝓑).presheaf.obj (op U)) :
    ((nativeProjectiveHomogeneousSMul 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (ell:S) q ell.property k).val.app (op U))
        (nativeIntegerTwistSectionFrame 𝓑 a ha k (op U) (fun p => hU p.2) r) =
      nativeIntegerTwistSectionFrame 𝓑 a ha (k+(q:ℤ)) (op U) (fun p => hU p.2)
        (nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU * r) := by
  apply Subtype.ext
  funext p
  rw [nativeProjectiveHomogeneousSMul_section_value]
  apply (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1).injective
  rw [nativeRingLocalization_original_smul, nativeIntegerTwistSectionFrame_localizedValue,
    nativeIntegerTwistSectionFrame_localizedValue]
  let u := nativePrimeCoordinateUnit 𝓑 p.1 a (hU p.2)
  change algebraMap S (Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) (ell:S) *
      ((↑(u^k) : Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) * (r.1 p).val) =
    (↑(u^(k+(q:ℤ))) : Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) *
      (((nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U hU).1 p) * r.1 p).val
  rw [HomogeneousLocalization.val_mul,
    ← nativeHomogeneousChartCoefficientSection_spec 𝓑 q ell a ha U hU p,
    zpow_add, Units.val_mul]
  ring

end LinearStudy
