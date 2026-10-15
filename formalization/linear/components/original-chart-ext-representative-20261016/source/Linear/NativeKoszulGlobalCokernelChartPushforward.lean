module
public import Linear.NativeKoszulCokernelChartFromPresentation
public import Linear.NativeKoszulSupportedCokernelUnit
public import Linear.SchemeModuleSupportedRestrictionIso
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
  nativeProjectiveKoszulCokernelChartFromPresentationIso
  tildeKoszulOriginalCutCokernelCofork schemeModuleSupportedRestrictionIso

/-- Identify the SAME original GLOBAL cokernel,for EVERY integer twist,
with the ACTUAL pushforward of the ORIGINAL affine cut structure sheaf.
The original chart cofork point is proved to be i_*O_Z in the existing
point theorem. Ambient cover is explicit;off-cut vanishing,native unit
invertibility and original chart identification are all DERIVED.
Comparison with the separately defined WHOLE projective-cut embedding
and its native line twist remains a separate obligation. -/
def nativeProjectiveKoszulGlobalCokernelChartPushforwardIso [IsNoetherianRing S]
    {J : Type} (b : J → S) (hb : ∀ t,b t ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1)
    (hc : ∀ x : Proj 𝓑,x ∈ Proj.basicOpen 𝓑 a ∨
      ∃ i : Fin r,x ∈ Proj.basicOpen 𝓑 (H i)) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let j := Proj.awayι 𝓑 a ha one_pos
    let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
      (by simpa using hH i)
    cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0) ≅
      (Scheme.Modules.pushforward j).obj (tildeKoszulOriginalCutCokernelCofork R h).pt := by
  let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
  let j := Proj.awayι 𝓑 a ha one_pos
  let h : Fin r → R := fun i => HomogeneousLocalization.Away.mk 𝓑 ha q (H i)
    (by simpa using hH i)
  exact schemeModuleSupportedRestrictionIso j _ _
    (nativeProjectiveKoszul_cokernelRestrictionUnit_isIso 𝓑 b hb hgen H hH k a ha hc)
    (nativeProjectiveKoszulCokernelChartFromPresentationIso 𝓑 b hb hgen H hH k a ha)

end LinearStudy
