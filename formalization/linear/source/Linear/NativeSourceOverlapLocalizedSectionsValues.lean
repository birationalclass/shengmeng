module
public import Linear.NativeSourceOverlapLocalizedSectionsEquiv
public import Linear.NativeGradedDegreeOneOverlapLocalization
public import Linear.NativeSourceSpecChartLinear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
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
/-- The SAME constructed overlap-to-sections equivalence preserves GENUINE restriction of every original chart element. -/
theorem nativeSourceOverlapLocalizedSectionsLinearEquiv_apply_overlap
    {ι : Type u} (coords : ι → S) (hcoords : ∀ i, coords i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range coords) = ⊤)
    (a b : S) (ha : a ∈ 𝓑 1) (hb : b ∈ 𝓑 1) (hab : a*b ≠ 0)
    (hs : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1 a ha))
    (x : nativeGradedModuleAwayDegreeZero 𝓑 𝒟 1 a) :
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let Q := F.restrict (Proj.awayι 𝓑 a ha (by decide))
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  letI := nativeGradedDegreeOneOverlapBaseModule 𝓑 𝒟 a b hb
  nativeSourceOverlapLocalizedSectionsLinearEquiv 𝓑 𝒟 hD coords hcoords hgen
      a b ha hb hab hs (nativeGradedModuleWeightedOverlapMap 𝓑 𝒟 hD 1 1 a b ha hb x) =
    Q.presheaf.map (PrimeSpectrum.basicOpen t).leTop.op
      (nativeSourceSpecChartSectionLinearMap 𝓑 𝒟 hD a ha
        ((LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝓑 𝒟 a)) x)) := by
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  let Q := F.restrict (Proj.awayι 𝓑 a ha (by decide))
  let t := HomogeneousLocalization.Away.isLocalizationElem ha hb
  letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(Q,PrimeSpectrum.basicOpen t) :=
    inferInstanceAs <| Module (HomogeneousLocalization.Away 𝓑 a)
      (((modulesSpecToSheaf (R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).obj Q).obj.obj
        (op (PrimeSpectrum.basicOpen t)))
  let P := Submonoid.powers t
  letI := nativeGradedDegreeOneOverlapBaseModule 𝓑 𝒟 a b hb
  letI := nativeGradedDegreeOneOverlap_isLocalizedModule 𝓑 𝒟 hD a b ha hb hab
  letI := nativeFiniteGradedChartOverlapSections_isLocalizedModule 𝓑 𝒟 hD
    coords hcoords hgen a b ha hb
  let f := nativeGradedDegreeOneOverlapLinearMap 𝓑 𝒟 hD a b ha hb
  let E1 := (LinearEquiv.ofEq _ _ (nativeGradedModuleAwayDegreeZero_one 𝓑 𝒟 a)).trans
    (LinearEquiv.ofBijective (nativeSourceSpecChartSectionLinearMap 𝓑 𝒟 hD a ha)
      (nativeSourceSpecChartSectionLinearMap_bijective 𝓑 𝒟 hD a ha hs))
  let ψ := ((modulesSpecToSheaf.obj Q).obj.map (PrimeSpectrum.basicOpen t).leTop.op).hom
  let g := ψ.comp E1.toLinearMap
  letI : IsLocalizedModule P g := inferInstance
  change IsLocalizedModule.linearEquiv P f g (f x) = g x
  exact IsLocalizedModule.linearEquiv_apply P f g x
end LinearStudy
