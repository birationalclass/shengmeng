module
public import Linear.MappedChainPresentationData
public import Linear.NativeKoszulMappedChartBoundary
public import Linear.TildeKoszulOriginalCutCofork
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulMappedTildeAffineIso tildeFunctionKoszulComplex
  tildeKoszulOriginalCutCokernelCofork tildeKoszulOriginalCutCokernelCoforkIsColimit
  mappedChainPresentationData chainCokernelProjectionInvariant
  CategoryTheory.Functor.mapHomologicalComplex

/-- Construct actual ORIGINAL source,chart complex,original chart map,
original quotient cofork and its proved colimit property. The desired
projection equality is not a field or premise. All integer twists and
the original quotient ideal/nilpotents are retained. -/
def nativeProjectiveKoszulMappedPresentationData [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let j := Proj.awayι 𝓑 a ha one_pos
    letI := schemeModuleOpenRestriction_additive j
    mappedChainPresentationData (Scheme.Modules.restrictFunctor j) := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  letI := schemeModuleOpenRestriction_additive j
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  unfold mappedChainPresentationData
  exact ⟨nativeProjectiveKoszulComplex 𝓑 H hH k,tildeFunctionKoszulComplex R h,
    nativeProjectiveKoszulMappedTildeAffineIso 𝓑 b hb hgen H hH k a ha,
    tildeKoszulOriginalCutCokernelCofork R h,tildeKoszulOriginalCutCokernelCoforkIsColimit R h⟩

end LinearStudy
