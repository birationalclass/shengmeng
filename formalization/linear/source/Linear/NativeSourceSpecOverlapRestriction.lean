module
public import Linear.NativeFiniteGradedChartOverlapLocalization
public import Linear.SchemeModuleSpecOpenSections
public import Linear.NativeProjectiveChartSectionsOverlap
public import Linear.NativeGradedDegreeOneOverlapLocalization
public import Linear.NativeSourceSpecChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M) [DirectSum.Decomposition 𝒟]
variable (hD : ∀ n : ℕ, ∀ j : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ m : M, m ∈ 𝒟 j → b • m ∈ 𝒟 ((n : ℤ)+j))
variable [IsNoetherianRing S] [Module.Finite S M] [IsDomain S] [Module.IsTorsionFree S M]
attribute [local instance] nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
  nativeSourceSpecChartSectionsModule
/-- The OLD weighted chart section map, restricted to an overlap, agrees
with genuine restriction of the SAME original one-chart section map under
actual Spec-chart transport. This is a map equality on every original element. -/
theorem nativeSourceSpecOverlapRestriction
    (a b : S) (ha : a ∈ 𝓑 1) (hb : b ∈ 𝓑 1)
    (x : nativeGradedModuleAwayDegreeZero 𝓑 𝒟 1 a) :
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let j := Proj.awayι 𝓑 a ha (by decide)
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  schemeModuleSpecOpenSectionsEquiv F j (PrimeSpectrum.basicOpen t)
      (Proj.basicOpen 𝓑 (a*b)) (nativeProjectiveChartRatioOpen_image 𝓑 a b ha hb)
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2 (a*b)
        (SetLike.mul_mem_graded ha hb)
        (nativeGradedModuleWeightedOverlapMap 𝓑 𝒟 hD 1 1 a b ha hb x)) =
    (F.restrict j).presheaf.map (PrimeSpectrum.basicOpen t).leTop.op
      (nativeSourceSpecChartSectionLinearMap 𝓑 𝒟 hD a ha
        ((LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝓑 𝒟 a)) x)) := by
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let j := Proj.awayι 𝓑 a ha (by decide)
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  have hi : j ''ᵁ ⊤ = Proj.basicOpen 𝓑 a :=
    j.image_top_eq_opensRange.trans (Proj.opensRange_awayι 𝓑 a ha (by decide))
  have H := schemeModuleSpecOpenSectionsEquiv_restrict F j
    (PrimeSpectrum.basicOpen t) ⊤ (Proj.basicOpen 𝓑 (a*b)) (Proj.basicOpen 𝓑 a)
    (nativeProjectiveChartRatioOpen_image 𝓑 a b ha hb) hi le_top
    (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 a ha x)
  have ho : F.presheaf.map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left 𝓑 a b)).op
      (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 a ha x) =
    nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 2 (a*b)
      (SetLike.mul_mem_graded ha hb)
      (nativeGradedModuleWeightedOverlapMap 𝓑 𝒟 hD 1 1 a b ha hb x) :=
    nativeProjectiveChartDegreeZeroSectionMap_overlap 𝓑 𝒟 hD 1 1 a b ha hb x
  exact (congrArg (schemeModuleSpecOpenSectionsEquiv F j
    (PrimeSpectrum.basicOpen t) (Proj.basicOpen 𝓑 (a*b))
    (nativeProjectiveChartRatioOpen_image 𝓑 a b ha hb)) ho).symm.trans H
end LinearStudy
