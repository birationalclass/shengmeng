module
public import Linear.NativeKoszulMappedPresentationData
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
  nativeProjectiveKoszulMappedPresentationData
  chainCokernelProjectionInvariant CategoryTheory.Functor.mapHomologicalComplex

/-- An ACTUAL proof term,whose proposition is inferred from applying the
already proved generic projection theorem to CONSTRUCTED ORIGINAL data.
This is NOT a definition of a proposition or a placeholder. The complete
inferred proposition MUST be separately printed and audited before this
can count as verified projection compatibility. Avoid a second large
expected-type elaboration of concrete complex fields. -/
def nativeProjectiveKoszulPresentationProjectionProof [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :=
  let j := Proj.awayι 𝓑 a ha one_pos
  letI := schemeModuleOpenRestriction_additive j
  letI := schemeModuleOpenRestriction_preservesHomology j
  let d := nativeProjectiveKoszulMappedPresentationData 𝓑 b hb hgen H hH k a ha
  mappedChainPresentationData_projection (Scheme.Modules.restrictFunctor j) d

end LinearStudy
