module
public import Linear.NativeProjectiveFiniteGradedQuasicoherent
public import Linear.NativeProjectiveChartSections
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsNoetherianRing S] [Module.Finite S M]
/-- The actual affine-chart ratio open is exactly the original Proj overlap,
not merely an isomorphic substitute for that open set. -/
theorem nativeProjectiveChartRatioOpen_image
    (a b : S) (ha : a ∈ 𝓑 1) (hb : b ∈ 𝓑 1) :
    (Proj.awayι 𝓑 a ha (by decide)) ''ᵁ
      PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem ha hb) =
      Proj.basicOpen 𝓑 (a*b) := by
  rw [← Proj.awayι_preimage_basicOpen 𝓑 ha (by decide) hb (by decide),
    Scheme.Hom.image_preimage_eq_opensRange_inf,Proj.opensRange_awayι,← Proj.basicOpen_mul]
/-- For the SAME actual native finite graded sheaf, restriction on its
actual affine chart to D(b/a) is module localization. Quasicoherence is
DERIVED from its finite graded generators, and the map is genuine restriction. -/
theorem nativeFiniteGradedChartOverlapSections_isLocalizedModule
    {ι : Type u} (coords : ι → S) (hcoords : ∀ i, coords i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range coords) = ⊤)
    (a b : S) (ha : a ∈ 𝓑 1) (hb : b ∈ 𝓑 1) :
    let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
    let Q := F.restrict (Proj.awayι 𝓑 a ha (by decide))
    let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
    IsLocalizedModule (Submonoid.powers t)
      ((modulesSpecToSheaf.obj Q).obj.map (PrimeSpectrum.basicOpen t).leTop.op).hom := by
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  letI : F.IsQuasicoherent := nativeFiniteGraded_isQuasicoherent 𝓑 𝒟 hD coords hcoords hgen
  let Q := F.restrict (Proj.awayι 𝓑 a ha (by decide))
  letI : Q.IsQuasicoherent := inferInstance
  exact (isIso_fromTildeΓ_iff_isLocalizing Q).mp inferInstance
    (HomogeneousLocalization.Away.isLocalizationElem ha hb)
end LinearStudy
