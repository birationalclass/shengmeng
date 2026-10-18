module
public import Linear.NativeKoszulOffCutCokernelZero
public import Linear.SchemeModuleSupportedRestrictionUnit
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

/-- Glue the SAME original global cokernel over the main chart and the
ORIGINAL equation-nonvanishing opens. Prove its ACTUAL native restriction
adjunction unit is an isomorphism,for EVERY integer twist. Actual ambient
coverage is EXPLICIT;the original geometric application derives it.
Off-cut zero restrictions are PROVED,not assumed. -/
theorem nativeProjectiveKoszul_cokernelRestrictionUnit_isIso
    {J : Type} (b : J → S) (hb : ∀ t,b t ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q)
    (k : ℤ) (a : S) (ha : a ∈ 𝓑 1)
    (hc : ∀ x : Proj 𝓑,x ∈ Proj.basicOpen 𝓑 a ∨
      ∃ i : Fin r,x ∈ Proj.basicOpen 𝓑 (H i)) :
    IsIso ((Scheme.Modules.restrictAdjunction (Proj.awayι 𝓑 a ha one_pos)).unit.app
      (cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0))) := by
  let M := cokernel ((nativeProjectiveKoszulComplex 𝓑 H hH k).d 1 0)
  let j := Proj.awayι 𝓑 a ha one_pos
  have hj : j ''ᵁ ⊤ = Proj.basicOpen 𝓑 a :=
    j.image_top_eq_opensRange.trans (Proj.opensRange_awayι 𝓑 a ha one_pos)
  apply schemeModule_restrictionUnit_isIso_of_originalCover j M
    (fun i : Fin r => Proj.basicOpen 𝓑 (H i))
  · intro x
    rw [hj]
    exact hc x
  · intro i W hW
    let U := Proj.basicOpen 𝓑 (H i)
    have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
      nativeProjectiveKoszul_cokernel_openRestriction_isZero_offCut
        𝓑 b hb hgen H hH i k U.ι (fun x => x.property)
    exact schemeModule_sections_isZero_of_openRestriction U.ι M hz W
      (hW.trans (le_of_eq U.ι_image_top.symm))

end LinearStudy
