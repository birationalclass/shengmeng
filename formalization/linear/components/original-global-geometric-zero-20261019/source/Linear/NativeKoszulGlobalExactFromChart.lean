module
public import Linear.NativeKoszulOffCutActualStalkExact
public import Linear.SchemeModuleActualStalkOpenRestriction
public import Linear.NativeGlobalKoszulAffineCounit
public import Linear.NativeProjectiveDegreeOneCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- GLOBAL exactness of the SAME original weighted Koszul follows from
its actual a-chart exactness and the actual cover by that chart plus
original equation-nonvanishing opens. The off-cut exactness is PROVED,
using original sections and native actual stalks,not an additional input.
The chart exactness and cover are explicit premises of this generic gluing
lemma; the original geometric wrapper derives BOTH independently. -/
theorem nativeProjectiveKoszul_global_exactAt_of_chart
    {J : Type} (b : J → S) (hb : ∀ i,b i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1)
    (hcover : ∀ x : Proj 𝓑,x ∈ Proj.basicOpen 𝓑 a ∨
      ∃ i : Fin r,x ∈ Proj.basicOpen 𝓑 (H i))
    (p : ℕ) (hp : 0 < p)
    (he : (nativeProjectiveKoszulOnAffine 𝓑
      (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))
      (Proj.awayι 𝓑 a ha one_pos) H hH k).ExactAt p) :
    (nativeProjectiveKoszulComplex 𝓑 H hH k).ExactAt p := by
  let C := nativeProjectiveKoszulComplex 𝓑 H hH k
  letI : (Scheme.Modules.toPresheaf (Proj 𝓑)).Additive := ⟨by intros; rfl⟩
  letI (x : Proj 𝓑) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat) x
  apply (schemeModuleComplex_exactAt_iff_actualAdditiveStalks C p).mpr
  intro x
  change (((Scheme.Modules.toPresheaf (Proj 𝓑) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj C).ExactAt p
  rcases hcover x with hxa | ⟨i,hxi⟩
  · let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let j := Proj.awayι 𝓑 a ha one_pos
    have himage : j ''ᵁ ⊤ = Proj.basicOpen 𝓑 a :=
      j.image_top_eq_opensRange.trans (Proj.opensRange_awayι 𝓑 a ha one_pos)
    rw [← himage] at hxa
    obtain ⟨z,_,hz⟩ := hxa
    subst x
    change ((C.sc p).map (Scheme.Modules.toPresheaf (Proj 𝓑) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat (j z))).Exact
    apply schemeModuleShortComplex_actualStalk_exact_of_openRestriction j (C.sc p) z
    exact he
  · have hxb : x ∈ ⨆ t : J,Proj.basicOpen 𝓑 (b t) := by
      rw [degreeOneGenerated_nativeProj_cover 𝓑 b hb hgen]
      trivial
    obtain ⟨t,hxt⟩ := Opens.mem_iSup.mp hxb
    exact nativeProjectiveKoszul_actualStalk_exactAt_offCut 𝓑 H hH i k (b t) (hb t) x hxt hxi p hp

end LinearStudy