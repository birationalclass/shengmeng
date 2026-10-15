module
public import Linear.MappedChainPresentationAugmentation
public import Linear.NativeKoszulMappedPresentationData
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulMappedPresentationData
  mappedChainPresentationAugmentationLaw

/-- The SAME ACTUAL original global Koszul/standard-affine complex iso,
original quotient cofork and proved colimit are constructed in ONE native
presentation payload. PROVE its whole actual augmentation square for
EVERY final target T and original cokernel identification ec. No desired
square or extra geometric comparison is assumed. -/
theorem nativeProjectiveKoszulPresentationAugmentationLaw [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let j := Proj.awayι 𝓑 a ha one_pos
    letI := schemeModuleOpenRestriction_additive j
    letI := schemeModuleOpenRestriction_preservesHomology j
    mappedChainPresentationAugmentationLaw (Scheme.Modules.restrictFunctor j)
      (nativeProjectiveKoszulMappedPresentationData 𝓑 b hb hgen H hH k a ha) := by
  let j := Proj.awayι 𝓑 a ha one_pos
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  exact mappedChainPresentationAugmentationLaw_proof (Scheme.Modules.restrictFunctor j)
    (nativeProjectiveKoszulMappedPresentationData 𝓑 b hb hgen H hH k a ha)

end LinearStudy
