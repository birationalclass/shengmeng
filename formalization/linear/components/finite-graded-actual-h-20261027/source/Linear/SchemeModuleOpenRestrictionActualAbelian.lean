module
public import Linear.TopOpenAbelianSheafRestriction
public import Linear.SchemeModuleFiniteSupportCohomology
public import Linear.SchemeModuleOpenRestrictionExact
public import Mathlib.CategoryTheory.Whiskering
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u
/-- Native O-module restriction and ACTUAL topological open restriction have the
SAME underlying abelian sheaf,including every section and every restriction map. -/
def schemeModuleOpenRestrictionActualAbelianIso (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ schemeModuleToActualAbelianSheaf U ≅
      schemeModuleToActualAbelianSheaf X ⋙ topOpenAbelianSheafRestriction X U :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (U : Scheme))
    AddCommGrpCat.{u}).whiskeringRight X.Modules).preimageIso
      (X := Scheme.Modules.restrictFunctor U.ι ⋙ schemeModuleToActualAbelianSheaf U)
      (Y := schemeModuleToActualAbelianSheaf X ⋙ topOpenAbelianSheafRestriction X U)
      (schemeModuleOpenRestriction_toPresheafIso U.ι)
end LinearStudy
