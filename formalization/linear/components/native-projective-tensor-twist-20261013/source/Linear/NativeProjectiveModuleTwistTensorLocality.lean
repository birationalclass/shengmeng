module
public import Linear.NativeProjectiveModuleTwistTensorMap
public import Linear.NativeProjectiveModuleTwistTensorChart
public import Linear.NativeProjectiveDegreeOneCover
public import Mathlib.Topology.Sheaves.LocallySurjective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S M : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup M] [Module S M] [Module K M]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K M)
variable (hD : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : M, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

/-- On every degree-one chart subopen, the actual tensor presheaf
multiplication is bijective; the inverse is the proved local frame. -/
theorem nativeProjectiveModuleTwistTensorPresheafMap_chart_bijective
    (a : S) (ha : a ∈ 𝓑 1) (m : ℕ) (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    Function.Bijective ((nativeProjectiveModuleTwistTensorPresheafMap 𝓑 𝒟 hD m k).app U) := by
  change Function.Bijective (TensorProduct.lift (nativeProjectiveModuleTwistPairing 𝓑 𝒟 hD m k U))
  rw [← nativeProjectiveModuleTwistTensorChartEquiv_eq_pairing 𝓑 𝒟 hD a ha m k U hp]
  exact (nativeProjectiveModuleTwistTensorChartEquiv 𝓑 𝒟 hD a ha m k U hp).bijective

variable {ι : Type u} (a : ι → S) (ha : ∀ i, a i ∈ 𝓑 1)
variable (hgen : Algebra.adjoin K (Set.range a) = ⊤)
include ha hgen

/-- The degree-one generators give actual local tensor preimages on
the original Proj site. No local-surjectivity certificate is an input. -/
theorem nativeProjectiveModuleTwistTensorPresheafMap_locallySurjective (m : ℕ) (k : ℤ) :
    PresheafOfModules.IsLocallySurjective
      (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝓑))
      (nativeProjectiveModuleTwistTensorPresheafMap 𝓑 𝒟 hD m k) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U f p hp
  have hpc : p ∈ ⨆ i, Proj.basicOpen 𝓑 (a i) := by
    rw [degreeOneGenerated_nativeProj_cover 𝓑 a ha hgen]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hpc
  let V := U ⊓ Proj.basicOpen 𝓑 (a i)
  let j : V ⟶ U := homOfLE inf_le_left
  obtain ⟨s, hs⟩ := (nativeProjectiveModuleTwistTensorPresheafMap_chart_bijective
    𝓑 𝒟 hD (a i) (ha i) m k (op V) (fun q => q.property.2)).2
      ((nativeProjectiveModulePresheaf 𝓑 𝒟 hD (k+(m : ℤ))).map j.op f)
  exact ⟨V, inf_le_left, ⟨s, hs⟩, ⟨hp, hi⟩⟩

/-- Equal actual tensor sections are locally equal before sheafification.
The covering neighborhoods are constructed from the degree-one generators. -/
theorem nativeProjectiveModuleTwistTensorPresheafMap_locallyInjective (m : ℕ) (k : ℤ) :
    PresheafOfModules.IsLocallyInjective
      (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝓑))
      (nativeProjectiveModuleTwistTensorPresheafMap 𝓑 𝒟 hD m k) := by
  constructor
  intro U x y h p hp
  have hpc : p ∈ ⨆ i, Proj.basicOpen 𝓑 (a i) := by
    rw [degreeOneGenerated_nativeProj_cover 𝓑 a ha hgen]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hpc
  let V := U.unop ⊓ Proj.basicOpen 𝓑 (a i)
  let j : V ⟶ U.unop := homOfLE inf_le_left
  refine ⟨V, j, ?_, ⟨hp, hi⟩⟩
  change (nativeProjectiveModuleTwistTensorPresheaf 𝓑 𝒟 hD m k).map j.op x =
    (nativeProjectiveModuleTwistTensorPresheaf 𝓑 𝒟 hD m k).map j.op y
  apply (nativeProjectiveModuleTwistTensorPresheafMap_chart_bijective
    𝓑 𝒟 hD (a i) (ha i) m k (op V) (fun q => q.property.2)).1
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  exact congrArg (fun z => (nativeProjectiveModulePresheaf 𝓑 𝒟 hD
    (k+(m : ℤ))).map j.op z) h

end LinearStudy
