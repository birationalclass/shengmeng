module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
/-- The actual ratio open for arbitrary positive second degree is the SAME
original weighted Proj intersection.No coefficient-module expansion is needed. -/
theorem nativeWeightedProjRatioOpen_image (e : ℕ) (he : 0 < e)
    (a b : S) (ha : a ∈ B 1) (hb : b ∈ B e) :
    (Proj.awayι B a ha (by decide)) ''ᵁ
      PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem ha hb) =
      Proj.basicOpen B (a*b) := by
  rw [← Proj.awayι_preimage_basicOpen B ha (by decide) hb he,
    Scheme.Hom.image_preimage_eq_opensRange_inf,Proj.opensRange_awayι,← Proj.basicOpen_mul]
end LinearStudy
