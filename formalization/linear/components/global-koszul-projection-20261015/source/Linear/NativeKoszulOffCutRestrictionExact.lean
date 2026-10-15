module
public import Linear.NativeKoszulOffCutAllDegrees
public import Linear.SchemeModuleActualStalkOpenRestrictionReverse
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

/-- On ANY ACTUAL open immersion whose image avoids one ORIGINAL equation,
the SAME original GLOBAL Koszul restricts to an exact complex in EVERY
nonnegative degree and EVERY integer twist. Derive the actual original
stalk exactness from the original degree-one cover and the original unit
equation; no local/global exactness certificate is assumed. -/
theorem nativeProjectiveKoszul_openRestriction_exactAt_offCut
    {J : Type} (b : J → S) (hb : ∀ t,b t ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range b) = ⊤)
    {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q)
    (i : Fin r) (k : ℤ) {X : Scheme} (j : X ⟶ Proj 𝓑) [IsOpenImmersion j]
    (hj : ∀ x : X,j x ∈ Proj.basicOpen 𝓑 (H i)) (p : ℕ) :
    letI := schemeModuleOpenRestriction_additive j
    (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (nativeProjectiveKoszulComplex 𝓑 H hH k)).ExactAt p := by
  letI := schemeModuleOpenRestriction_additive j
  letI : (Scheme.Modules.toPresheaf X).Additive := ⟨by intros; rfl⟩
  letI : (Scheme.Modules.toPresheaf (Proj 𝓑)).Additive := ⟨by intros; rfl⟩
  letI (x : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat) x
  letI (x : Proj 𝓑) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat) x
  let C := nativeProjectiveKoszulComplex 𝓑 H hH k
  change ((C.sc p).map (Scheme.Modules.restrictFunctor j)).Exact
  apply (schemeModuleShortComplex_openRestriction_exact_iff_actualStalks j (C.sc p)).mpr
  intro x
  have hxb : j x ∈ ⨆ t : J,Proj.basicOpen 𝓑 (b t) := by
    rw [degreeOneGenerated_nativeProj_cover 𝓑 b hb hgen]
    trivial
  obtain ⟨t,hxt⟩ := Opens.mem_iSup.mp hxb
  exact nativeProjectiveKoszul_actualStalk_exactAt_offCut_all 𝓑 H hH i k
    (b t) (hb t) (j x) hxt (hj x) p

end LinearStudy
