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
attribute [local irreducible] nativeProjectiveKoszulOnAffine nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveKoszulNamedTildeAffineIso tildeFunctionKoszulComplex

/-- Apply the native homology functor to the PROVED entire original
standard-affine complex comparison. It retains the SAME original
coefficient fractions and ALL integer twists;no homology comparison input. -/
def nativeProjectiveKoszulStandardAffineHomologyIso [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (p : ℕ) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let j := Proj.awayι 𝓑 a ha one_pos
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)
    (HomologicalComplex.homologyFunctor (Spec R).Modules (ComplexShape.down ℕ) p).obj
      (nativeProjectiveKoszulOnAffine 𝓑 R j H hH k) ≅
      (HomologicalComplex.homologyFunctor (Spec R).Modules (ComplexShape.down ℕ) p).obj
        (tildeFunctionKoszulComplex R h) := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  exact (HomologicalComplex.homologyFunctor (Spec R).Modules (ComplexShape.down ℕ) p).mapIso
    (nativeProjectiveKoszulNamedTildeAffineIso 𝓑 b hb hgen H hH k a ha)

end LinearStudy