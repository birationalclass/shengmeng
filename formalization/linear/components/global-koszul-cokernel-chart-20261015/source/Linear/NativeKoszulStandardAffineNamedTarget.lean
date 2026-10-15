module
public import Linear.NativeGlobalKoszulAffineStandard
public import Linear.TildeComplexExact
import all Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulStandardAffineIso
  nativeProjectiveKoszulOnAffine nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- Name the SAME actual native tilde Koszul target of the ALREADY proved
whole original standard-affine comparison. Every source/differential and
integer twist is unchanged;no comparison or exactness is an assumption. -/
def nativeProjectiveKoszulNamedTildeAffineIso [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let j := Proj.awayι 𝓑 a ha one_pos
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)
    nativeProjectiveKoszulOnAffine 𝓑 R j H hH k ≅ tildeFunctionKoszulComplex R h := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  letI : (tilde.functor R).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor (R := R)
  exact nativeProjectiveKoszulStandardAffineIso 𝓑 b hb hgen H hH k a ha

end LinearStudy