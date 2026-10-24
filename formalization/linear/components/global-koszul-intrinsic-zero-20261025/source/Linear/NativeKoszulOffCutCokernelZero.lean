module
public import Linear.NativeKoszulOffCutRestrictionExact
public import Linear.ChainFirstCokernelZero
public import Linear.SchemeModuleRestrictionCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- The ACTUAL original global d1-cokernel restricts to ZERO on any
ACTUAL open immersion whose image avoids one ORIGINAL equation,for EVERY
integer twist. Both restricted source exactness and the original
restriction-cokernel comparison are DERIVED from already proved actual
maps;neither desired vanishing nor any regularity is an input. -/
theorem nativeProjectiveKoszul_cokernel_openRestriction_isZero_offCut
    {J : Type} (b : J → S) (hb : ∀ t,b t ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q)
    (i : Fin r) (k : ℤ) {X : Scheme} (j : X ⟶ Proj 𝓑) [IsOpenImmersion j]
    (hj : ∀ x : X,j x ∈ Proj.basicOpen 𝓑 (H i)) :
    IsZero ((Scheme.Modules.restrictFunctor j).obj
      (cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0))) := by
  letI := schemeModuleOpenRestriction_additive j
  let C := nativeProjectiveKoszulComplex 𝓑 H hH k
  let E := ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C
  have he : E.ExactAt 0 := nativeProjectiveKoszul_openRestriction_exactAt_offCut
    𝓑 b hb hgen H hH i k j hj 0
  have hz := originalChainFirstCokernel_isZero_of_exactAt_zero E he
  exact hz.of_iso (schemeModuleOpenRestrictionCokernelIso j (C.d 1 0))

end LinearStudy
