module
public import Linear.NativeIntegerTwistChartSingleFraction
public import Linear.NativeProjectiveShiftedFreePrimeIdentities
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S ι : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [Fintype ι] [DecidableEq ι] (w : ι → ℤ)
attribute [local instance] LocalizedModule.moduleOfIsLocalization
  nativeHomogeneousAwayModuleScalar nativeProjectiveAtPrimeModuleScalar
  nativeProjectiveAmbientSectionModule

/-- The actual chart-to-section map for a finite shifted free graded
module is surjective. Each coordinate section is an actual homogeneous
fraction; original coordinate inclusions exhaust the localized module. -/
theorem nativeShiftedFreeChartDegreeZeroSectionMap_surjective
    (a : S) (ha : a ∈ 𝓑 1) :
    Function.Surjective (nativeProjectiveChartDegreeZeroSectionMap 𝓑
      (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) 1 a ha) := by
  intro f
  have hfrac : ∀ i : ι, ∃ n : ℕ, ∃ ell : S,
      ell ∈ nativeProjectiveRingIntegerPiece 𝓑 ((n : ℤ)+ -w i) ∧
      ∀ p : ProjectiveSpectrum.basicOpen 𝓑 a,
        (nativeShiftedFreeCoordinateSectionProjection 𝓑 w i
          (op (ProjectiveSpectrum.basicOpen 𝓑 a)) f).1 p =
          LocalizedModule.mk ell
            (⟨a^n,p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem p.2 n⟩ :
              p.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
    intro i
    exact nativeIntegerTwistChart_section_singleFraction 𝓑 a ha (-w i)
      (nativeShiftedFreeCoordinateSectionProjection 𝓑 w i
        (op (ProjectiveSpectrum.basicOpen 𝓑 a)) f)
  choose n ell hell hf using hfrac
  let x : ι → LocalizedModule (Submonoid.powers a) (ι → S) := fun i =>
    LocalizedModule.mk (Pi.single i (ell i)) (⟨a^(n i),⟨n i,rfl⟩⟩ : Submonoid.powers a)
  have hx : ∀ i : ι, x i ∈ nativeGradedModuleAwayDegreeZero 𝓑
      (integerShiftedFreePiece 𝓑 w) 1 a := by
    intro i
    apply Submodule.subset_span
    refine ⟨n i,Pi.single i (ell i),?_,rfl⟩
    have h := integerShiftedFreeSingle_homogeneous 𝓑 w i
      ((n i : ℤ)+ -w i) (ell i) (hell i)
    simpa only [mul_one,add_assoc,neg_add_cancel,add_zero,
      LinearMap.single_apply] using h
  refine ⟨⟨∑ i : ι, x i,Submodule.sum_mem _ (fun i _ => hx i)⟩,?_⟩
  apply Subtype.ext
  funext p
  change originalLocalizedModuleRefinement (Submonoid.powers a)
    p.1.asHomogeneousIdeal.toIdeal.primeCompl (Submonoid.powers_le.mpr p.2)
      (∑ i : ι,x i) = f.1 p
  rw [map_sum]
  rw [← nativeShiftedFreePrime_coordinate_total 𝓑 p.1 (f.1 p)]
  apply Finset.sum_congr rfl
  intro i hi
  have hfi := hf i p
  change nativeProjectiveModuleAtPrimeMap 𝓑
    (LinearMap.proj (R := S) (φ := fun _ : ι => S) i) p.1 (f.1 p) = _ at hfi
  rw [hfi,nativeProjectiveModuleAtPrimeMap_mk]
  dsimp only [x]
  rw [originalLocalizedModuleRefinement_mk]
  rfl

end LinearStudy
