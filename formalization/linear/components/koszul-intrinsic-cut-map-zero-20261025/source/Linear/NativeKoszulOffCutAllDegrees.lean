module
public import Linear.NativeKoszulOffCutActualStalkExact
public import Linear.KoszulFunctionUnitAllDegrees
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

/-- On EVERY actual subopen of D_+(a) intersect D_+(H_i),the SAME
original GLOBAL Koszul SECTION complex is exact in ALL nonnegative degrees at EVERY integer
twist. The SAME original H_i/a^q is proved to be a unit; the original
coordinate/exterior chain isomorphisms transport unit-Koszul exactness.
No regular sequence,local/global exactness or coefficient assumption. -/
theorem nativeProjectiveKoszul_sections_exactAt_offCut_all {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (i : Fin r) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (hcut : U ≤ Proj.basicOpen 𝓑 (H i))
    (p : ℕ) :
    (((SheafOfModules.forget (Proj 𝓑).ringCatSheaf ⋙
      PresheafOfModules.evaluation (Proj 𝓑).ringCatSheaf.obj (op U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (nativeProjectiveKoszulComplex 𝓑 H hH k)).ExactAt p := by
  let h : Fin r → (Proj 𝓑).presheaf.obj (op U) :=
    fun l => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU
  have hu : IsUnit (h i) :=
    nativeHomogeneousChartCoefficientSection_isUnit 𝓑 q ⟨H i,hH i⟩ a ha U hU hcut
  have he := functionKoszul_unit_exactAt_all h i hu p
  have hc := he.of_iso (homogeneousKoszulCoordinateComplexIso h)
  exact hc.of_iso (nativeGlobalKoszulChartSectionComplexIso 𝓑 H hH k a ha U hU).symm


/-- The SAME actual original global Koszul is exact on its ACTUAL
additive stalk at any point of D_+(a) intersect D_+(H_i),for ALL integer
twists and ALL p including ZERO. Exactness follows from proved original section exactness on EVERY
smaller open,not an abstract stalk model or local-exactness certificate. -/
theorem nativeProjectiveKoszul_actualStalk_exactAt_offCut_all {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (i : Fin r) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (x : Proj 𝓑)
    (hxa : x ∈ Proj.basicOpen 𝓑 a) (hxH : x ∈ Proj.basicOpen 𝓑 (H i))
    (p : ℕ) :
    letI : (Scheme.Modules.toPresheaf (Proj 𝓑)).Additive := ⟨by intros; rfl⟩
    letI : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat) x
    (((Scheme.Modules.toPresheaf (Proj 𝓑) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat x).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (nativeProjectiveKoszulComplex 𝓑 H hH k)).ExactAt p := by
  letI : (Scheme.Modules.toPresheaf (Proj 𝓑)).Additive := ⟨by intros; rfl⟩
  letI : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat) x
  let C := nativeProjectiveKoszulComplex 𝓑 H hH k
  let U := Proj.basicOpen 𝓑 a ⊓ Proj.basicOpen 𝓑 (H i)
  have hxU : x ∈ U := ⟨hxa,hxH⟩
  have hs := additivePresheafShortComplex_stalk_exact_of_nearby_sections
    ((C.sc p).map (Scheme.Modules.toPresheaf (Proj 𝓑))) x U hxU (by
      intro W hW t ht
      have he := nativeProjectiveKoszul_sections_exactAt_offCut_all 𝓑 H hH i k a ha W
        (hW.trans inf_le_left) (hW.trans inf_le_right) p
      exact (ShortComplex.moduleCat_exact_iff _).mp he t ht)
  change ((C.sc p).map (Scheme.Modules.toPresheaf (Proj 𝓑) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat x)).Exact
  simpa only [ShortComplex.map_comp] using hs


end LinearStudy
