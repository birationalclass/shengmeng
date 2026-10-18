module
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
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  tildeFunctionKoszulComplex tildeKoszulOriginalCutCokernelCofork
  chainCokernelProjectionInvariant CategoryTheory.Functor.mapHomologicalComplex

/-- The constructed chart data's source is EXACTLY the SAME original
native global Koszul complex,not a replacement model. -/
theorem nativeProjectiveKoszulMappedPresentationData_source [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    (nativeProjectiveKoszulMappedPresentationData 𝓑 b hb hgen H hH k a ha).1 =
      nativeProjectiveKoszulComplex 𝓑 H hH k := rfl

/-- Its quotient target is the SAME ORIGINAL quotient cofork point. -/
theorem nativeProjectiveKoszulMappedPresentationData_quotientTarget [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)
    (nativeProjectiveKoszulMappedPresentationData 𝓑 b hb hgen H hH k a ha).2.2.2.1.pt =
      (tildeKoszulOriginalCutCokernelCofork R h).pt := rfl

end LinearStudy
