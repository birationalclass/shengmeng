module
public import Linear.NativeKoszulPresentationGlobalProjectionExistsProof
public import Linear.SchemeModuleOriginalQuotientAugmentationProof
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  nativeProjectiveKoszulMappedPresentationData tildeKoszulOriginalCutCokernelCofork
  CategoryTheory.Functor.mapHomologicalComplex

/-- Construct the native global projection from ORIGINAL ambient coverage,
then transport its actual chart target to the SAME literal original
quotient cofork point. Leave the final target and its comparison abstract
at this boundary, so no concrete dependent payload is rebuilt. -/
def nativeProjectiveKoszulOriginalQuotientAugmentationProof [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1)
    (hc : ∀ x : Proj 𝓑,x ∈ Proj.basicOpen 𝓑 a ∨
      ∃ i : Fin r,x ∈ Proj.basicOpen 𝓑 (H i)) :=
  let j := Proj.awayι 𝓑 a ha one_pos
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  let d := nativeProjectiveKoszulMappedPresentationData 𝓑 b hb hgen H hH k a ha
  schemeModuleOriginalQuotientAugmentationProof j d _
    (nativeProjectiveKoszulMappedPresentationData_quotientTarget 𝓑 b hb hgen H hH k a ha)
    (nativeProjectiveKoszulPresentationGlobalProjectionExistsProof 𝓑 b hb hgen H hH k a ha hc)

end LinearStudy
