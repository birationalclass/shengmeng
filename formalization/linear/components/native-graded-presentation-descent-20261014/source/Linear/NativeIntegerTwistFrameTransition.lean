module
public import Linear.NativeIntegerTwistSectionFrames
public import Linear.NativeCoordinateRatio
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Changing the actual integer-twist frame from b to a multiplies its
structure-ring coefficient by the actual section (b/a)^k. This is proved
on every original open where both coordinates are nonvanishing. -/
theorem nativeIntegerTwistSectionFrame_transition (a : S) (ha : a ∈ 𝓑 1)
    (b : S) (hb : b ∈ 𝓑 1) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hpa : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (hpb : ∀ p : U.unop, b ∉ p.1.asHomogeneousIdeal)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) :
    nativeIntegerTwistSectionFrame 𝓑 b hb k U hpb r =
      nativeIntegerTwistSectionFrame 𝓑 a ha k U hpa
        ((((nativeCoordinateRatioUnit 𝓑 b hb a ha U hpb hpa)^k :
          ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)ˣ) :
            (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U) * r) := by
  apply Subtype.ext
  funext p
  apply (nativeProjectiveRingModuleLocalizationEquiv 𝓑 p.1).injective
  rw [nativeIntegerTwistSectionFrame_localizedValue,
    nativeIntegerTwistSectionFrame_localizedValue]
  change _ * (nativeStructureSectionPointRingHom 𝓑 U p) r =
    _ * (nativeStructureSectionPointRingHom 𝓑 U p) (_ * r)
  rw [map_mul, nativeCoordinateRatioUnit_zpow_pointValue]
  let ua := nativePrimeCoordinateUnit 𝓑 p.1 a (hpa p)
  let ub := nativePrimeCoordinateUnit 𝓑 p.1 b (hpb p)
  change (↑(ub^k) : Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) * _ =
    (↑(ua^k) : Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) *
      ((↑((ub * ua⁻¹)^k) : Localization p.1.asHomogeneousIdeal.toIdeal.primeCompl) * _)
  rw [← mul_assoc, ← Units.val_mul]
  congr 1
  apply congrArg Units.val
  simp [mul_zpow, mul_comm, mul_left_comm]

end LinearStudy
