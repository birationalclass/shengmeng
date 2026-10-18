module
public import Linear.SchemeModuleActualStalkExact
public import Linear.SchemeModuleOpenRestrictionExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Native actual open-immersion stalk comparison transports exactness
of the SAME restricted short complex back to the SAME original stalk.
The restriction/stalk isomorphism is mathlib's restrictStalkNatIso. -/
theorem schemeModuleShortComplex_actualStalk_exact_of_openRestriction
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (S : ShortComplex Y.Modules) (x : X) :
    letI := schemeModuleOpenRestriction_additive j
    letI : (Scheme.Modules.toPresheaf X).Additive := ⟨by intros; rfl⟩
    letI : (Scheme.Modules.toPresheaf Y).Additive := ⟨by intros; rfl⟩
    letI (z : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
    letI (z : Y) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
    (S.map (Scheme.Modules.restrictFunctor j)).Exact →
      (S.map (Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j x))).Exact := by
  letI := schemeModuleOpenRestriction_additive j
  letI : (Scheme.Modules.toPresheaf X).Additive := ⟨by intros; rfl⟩
  letI : (Scheme.Modules.toPresheaf Y).Additive := ⟨by intros; rfl⟩
  letI (z : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
  letI (z : Y) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
  intro he
  have hx := (schemeModuleShortComplex_exact_iff_actualAdditiveStalks
    (S.map (Scheme.Modules.restrictFunctor j))).mp he x
  have hx' : (S.map (Scheme.Modules.restrictFunctor j ⋙
      Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact := by
    change (S.map (Scheme.Modules.restrictFunctor j ⋙
      Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact at hx
    exact hx
  exact ShortComplex.exact_of_iso (S.mapNatIso (Scheme.Modules.restrictStalkNatIso j x)) hx'

end LinearStudy