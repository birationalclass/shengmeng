module
public import Linear.NativeKoszulPresentationDataObjects
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm
  tildeFunctionKoszulComplex tildeKoszulOriginalCutCokernelCofork
  chainCokernelProjectionInvariant CategoryTheory.Functor.mapHomologicalComplex
/-- The actual chart complex in the PREVIOUSLY CONSTRUCTED native payload.
Minimal imports retain its original ring/typeclass bindings. The proof
uses reflexivity at the actual payload projection, not a desired class law. -/
theorem nativeKoszulMappedChartComplex_identity [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ B 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ B q) (k : ℤ)
    (z : S) (hz : z ∈ B 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away B z)
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk B hz q (H i)
      (by simpa using hH i)
    (nativeProjectiveKoszulMappedPresentationData B b hb hgen H hH k z hz).2.1 =
      tildeFunctionKoszulComplex R h :=
  Eq.refl ((nativeProjectiveKoszulMappedPresentationData B b hb hgen H hH k z hz).2.1)
end LinearStudy

