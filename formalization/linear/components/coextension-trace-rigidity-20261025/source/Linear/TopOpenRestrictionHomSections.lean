module
public import Linear.TopOpenAbelianSheafRestriction
public import Linear.TopOpenFreeAbelianSheafAddSections
public import Linear.TopAbelianSheafIntegerSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Global sections after ACTUAL restriction are sections on SAME original open. -/
def topOpenRestrictionGlobalSectionsIso (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((topOpenAbelianSheafRestriction X U).obj F).obj.obj (op ⊤) ≅ F.obj.obj (op U) := by
  change F.obj.obj (op (U.isOpenEmbedding.functor.obj ⊤)) ≅ F.obj.obj (op U)
  exact F.obj.mapIso (eqToIso (by simp))
/-- SAME section identification is natural in EVERY coefficient morphism. -/
theorem topOpenRestrictionGlobalSectionsIso_naturality (X : TopCat.{u}) (U : Opens X)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    ((topOpenAbelianSheafRestriction X U).map f).hom.app (op ⊤) ≫
      (topOpenRestrictionGlobalSectionsIso X U G).hom =
    (topOpenRestrictionGlobalSectionsIso X U F).hom ≫ f.hom.app (op U) := by
  change f.hom.app (op (U.isOpenEmbedding.functor.obj ⊤)) ≫
      G.obj.map (eqToHom (by simp)) = F.obj.map (eqToHom (by simp)) ≫ f.hom.app (op U)
  exact (f.hom.naturality (eqToHom (by simp))).symm
/-- An actual Hom equivalence between free-open sources and restricted native integers. -/
def topOpenRestrictionHomAddEquiv (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((topOpenFreeAbelianSheafFunctor X).obj U ⟶ F) ≃+
      (((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
        (topOpenAbelianSheafRestriction X U).obj F) :=
  (topOpenFreeAbelianSheafHomSectionsAddEquiv X U F).trans
    ((topOpenRestrictionGlobalSectionsIso X U F).addCommGroupIsoToAddEquiv.symm.trans
      (topAbelianSheafIntegerHomSectionsAddEquiv _ _).symm)
/-- The ACTUAL Hom equivalence commutes with postcomposition by every coefficient map. -/
theorem topOpenRestrictionHomAddEquiv_postcompose (X : TopCat.{u}) (U : Opens X)
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (a : (topOpenFreeAbelianSheafFunctor X).obj U ⟶ F) :
    topOpenRestrictionHomAddEquiv X U G (a ≫ f) =
      topOpenRestrictionHomAddEquiv X U F a ≫ (topOpenAbelianSheafRestriction X U).map f := by
  let eF := (topOpenRestrictionGlobalSectionsIso X U F).addCommGroupIsoToAddEquiv
  let eG := (topOpenRestrictionGlobalSectionsIso X U G).addCommGroupIsoToAddEquiv
  apply (topAbelianSheafIntegerHomSectionsAddEquiv _ _).injective
  rw [topAbelianSheafIntegerHomSectionsAddEquiv_postcompose]
  simp only [topOpenRestrictionHomAddEquiv,AddEquiv.trans_apply,AddEquiv.apply_symm_apply]
  apply eG.injective
  change eG (eG.symm ((topOpenFreeAbelianSheafHomSectionsAddEquiv X U G) (a ≫ f))) =
    eG ((((topOpenAbelianSheafRestriction X U).map f).hom.app (op ⊤))
      (eF.symm ((topOpenFreeAbelianSheafHomSectionsAddEquiv X U F) a)))
  rw [AddEquiv.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom (topOpenRestrictionGlobalSectionsIso_naturality X U f)
    (eF.symm ((topOpenFreeAbelianSheafHomSectionsAddEquiv X U F) a))
  change eG ((((topOpenAbelianSheafRestriction X U).map f).hom.app (op ⊤))
      (eF.symm ((topOpenFreeAbelianSheafHomSectionsAddEquiv X U F) a))) =
    f.hom.app (op U) (eF (eF.symm ((topOpenFreeAbelianSheafHomSectionsAddEquiv X U F) a))) at hn
  rw [AddEquiv.apply_symm_apply] at hn
  rw [hn]
  exact topOpenFreeAbelianSheafHomEquiv_postcompose X U f a
end LinearStudy
