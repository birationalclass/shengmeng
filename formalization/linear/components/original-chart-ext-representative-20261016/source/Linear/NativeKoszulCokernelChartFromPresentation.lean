module
public import Linear.MappedChainCokernelPresentation
public import Linear.TildeKoszulOriginalCutCofork
public import Linear.NativeKoszulStandardAffineNamedTarget
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
  tildeFunctionKoszulComplex tildeKoszulPresentation nativeProjectiveKoszulNamedTildeAffineIso
  mappedChainFirstCokernelPresentationIso tildeKoszulOriginalCutCokernelCofork
  tildeKoszulOriginalCutCokernelCoforkIsColimit

/-- Construct the ORIGINAL global d1-cokernel chart comparison by applying
one GENERIC cokernel-presentation theorem,composed BEFORE specialization.
The target cofork point is PROVED to be the SAME original quotient-cut
structure sheaf;its universal property is DERIVED from actual exactness/epi.
ALL integer twists and nilpotents retained. The named original quotient cofork target avoids
redundant expansion of concrete large homology objects. No desired comparison,
positive source exactness or regularity is an input. -/
def nativeProjectiveKoszulCokernelChartFromPresentationIso [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let j := Proj.awayι 𝓑 a ha one_pos
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)
    (Scheme.Modules.restrictFunctor j).obj
      (cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0)) ≅
      (tildeKoszulOriginalCutCokernelCofork R h).pt :=
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  let F := Scheme.Modules.restrictFunctor j
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  mappedChainFirstCokernelPresentationIso F
    (nativeProjectiveKoszulComplex 𝓑 H hH k) (tildeFunctionKoszulComplex R h)
    (nativeProjectiveKoszulNamedTildeAffineIso 𝓑 b hb hgen H hH k a ha)
    (tildeKoszulOriginalCutCokernelCofork R h)
    (tildeKoszulOriginalCutCokernelCoforkIsColimit R h)

end LinearStudy