module
public import Linear.NativeKoszulStandardAffineNamedTarget
public import Linear.ChainFirstCokernelIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulOnAffine nativeProjectiveKoszulComplex
  nativeProjectiveKoszulTerm nativeProjectiveKoszulNamedTildeAffineIso tildeFunctionKoszulComplex

/-- Transport the actual ORIGINAL d1 cokernel through the ALREADY proved
whole standard-affine complex iso. No desired cokernel comparison input. -/
def nativeProjectiveKoszulStandardAffineCokernelIso [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let j := Proj.awayι 𝓑 a ha one_pos
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)
    cokernel ((nativeProjectiveKoszulOnAffine 𝓑 R j H hH k).d 1 0) ≅
      cokernel ((tildeFunctionKoszulComplex R h).d 1 0) := by
  exact originalChainFirstCokernelIso _ _
    (nativeProjectiveKoszulNamedTildeAffineIso 𝓑 b hb hgen H hH k a ha)

end LinearStudy
