module
public import Linear.NativeKoszulStandardAffineNamedTarget
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
  nativeProjectiveKoszulNamedTildeAffineIso tildeFunctionKoszulComplex
  CategoryTheory.Functor.mapHomologicalComplex

/-- The SAME original native chart map,with its source expressed as the
LITERAL mapped original complex. Keep the mapped-complex functor opaque
while converting the existing source alias;this avoids eager expansion
of its implicit-reducible implementation. No map or desired equality is
an input. This construction alone is not augmentation compatibility. -/
def nativeProjectiveKoszulMappedTildeAffineIso [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let j := Proj.awayι 𝓑 a ha one_pos
    letI := schemeModuleOpenRestriction_additive j
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)
    (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (nativeProjectiveKoszulComplex 𝓑 H hH k)) ≅ tildeFunctionKoszulComplex R h := by
  exact nativeProjectiveKoszulNamedTildeAffineIso 𝓑 b hb hgen H hH k a ha

end LinearStudy
