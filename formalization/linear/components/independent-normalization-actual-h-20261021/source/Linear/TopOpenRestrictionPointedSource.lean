module
public import Linear.TopOpenRestrictionHomSections
public import Linear.PointedExactFunctorExtZeroHomEquiv
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
universe u
/-- The actual point ℤ_U→(ℤ[U])|U is selected by the proved original Hom equivalence. -/
def topOpenRestrictionIntegerPoint (X : TopCat.{u}) (U : Opens X) :
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶
    (topOpenAbelianSheafRestriction X U).obj ((topOpenFreeAbelianSheafFunctor X).obj U) :=
  topOpenRestrictionHomAddEquiv X U _ (𝟙 _)
/-- The actual point induces EXACTLY the original free-open/restricted-integer Hom map. -/
theorem topOpenRestrictionIntegerPoint_comp (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : (topOpenFreeAbelianSheafFunctor X).obj U ⟶ F) :
    topOpenRestrictionIntegerPoint X U ≫ (topOpenAbelianSheafRestriction X U).map a =
      topOpenRestrictionHomAddEquiv X U F a := by
  simpa only [Category.id_comp,topOpenRestrictionIntegerPoint] using
    (topOpenRestrictionHomAddEquiv_postcompose X U a (𝟙 _)).symm
/-- The native exact-functor pointed Ext map is bijective in degree zero by ACTUAL
Hom equivalence,not by a desired higher-cohomology comparison hypothesis. -/
theorem topOpenRestrictionPointedExt_zero_bijective (X : TopCat.{u}) (U : Opens X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Bijective (pointedExactFunctorExtMap (topOpenAbelianSheafRestriction X U)
      (topOpenRestrictionIntegerPoint X U) F 0) := by
  exact pointedExactFunctorExtMap_zero_bijective_of_homEquiv
    (topOpenAbelianSheafRestriction X U) (topOpenRestrictionIntegerPoint X U) F
    (topOpenRestrictionHomAddEquiv X U F).toEquiv
    (fun a => topOpenRestrictionIntegerPoint_comp X U F a)
end LinearStudy
