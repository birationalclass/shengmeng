module
public import Linear.SchemeModuleActualStalkOpenRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- The SAME original short complex restricted along an ACTUAL open
immersion is exact iff its ACTUAL original additive stalks on that open
are exact. Native restrictStalkNatIso transports both implications. -/
theorem schemeModuleShortComplex_openRestriction_exact_iff_actualStalks
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (S : ShortComplex Y.Modules) :
    letI := schemeModuleOpenRestriction_additive j
    letI : (Scheme.Modules.toPresheaf X).Additive := ⟨by intros; rfl⟩
    letI : (Scheme.Modules.toPresheaf Y).Additive := ⟨by intros; rfl⟩
    letI (z : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
    letI (z : Y) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
      TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
    (S.map (Scheme.Modules.restrictFunctor j)).Exact ↔ ∀ x : X,
      (S.map (Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j x))).Exact := by
  letI := schemeModuleOpenRestriction_additive j
  letI : (Scheme.Modules.toPresheaf X).Additive := ⟨by intros; rfl⟩
  letI : (Scheme.Modules.toPresheaf Y).Additive := ⟨by intros; rfl⟩
  letI (z : X) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
  letI (z : Y) : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).Additive :=
    TopCat.instAdditivePresheafStalkFunctor (C := AddCommGrpCat.{u}) z
  constructor
  · intro he x
    exact schemeModuleShortComplex_actualStalk_exact_of_openRestriction j S x he
  · intro he
    apply (schemeModuleShortComplex_exact_iff_actualAdditiveStalks
      (S.map (Scheme.Modules.restrictFunctor j))).mpr
    intro x
    change (S.map (Scheme.Modules.restrictFunctor j ⋙
      Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).Exact
    exact ShortComplex.exact_of_iso
      (S.mapNatIso (Scheme.Modules.restrictStalkNatIso j x).symm) (he x)

end LinearStudy
