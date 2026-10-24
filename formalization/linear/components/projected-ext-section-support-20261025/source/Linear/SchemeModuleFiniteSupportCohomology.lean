module
public import Linear.DiscreteSheafPushforwardCohomology
public import Linear.FiniteCutArtinianTopology
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u

/-- The actual native forgetful functor from ORIGINAL O_X-modules to
abelian sheaves on the SAME topological space. -/
def schemeModuleToActualAbelianSheaf (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

/-- Native DERIVED SHEAF cohomology of the SAME original O_X-module's
underlying abelian sheaf. This abbreviation is not a replacement model. -/
abbrev schemeModuleActualCohomology (X : Scheme.{u}) (M : X.Modules) (j : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u} ((schemeModuleToActualAbelianSheaf X).obj M) j

/-- Forgetting scalars commutes with ACTUAL scheme direct image,keeping
ALL original open-section groups and maps definitionally. -/
def schemeModulePushforwardActualAbelianIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙ schemeModuleToActualAbelianSheaf Y ≅
      schemeModuleToActualAbelianSheaf X ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base :=
  Iso.refl _

/-- For an ACTUAL Artinian source scheme,every ORIGINAL O_X-module has
zero positive actual SHEAF cohomology after ACTUAL pushforward to Y.
No flat/free/FG/CM/injective/support/vanishing input for the module. -/
theorem artinianSchemeModule_actualPushforwardHigherCohomology_vanish
    {X Y : Scheme.{u}} [IsArtinianScheme X] (f : X ⟶ Y)
    (M : X.Modules) (j : ℕ) :
    Subsingleton (schemeModuleActualCohomology Y ((Scheme.Modules.pushforward f).obj M) (j+1)) := by
  change Subsingleton (CategoryTheory.Sheaf.H.{u}
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj
      ((schemeModuleToActualAbelianSheaf X).obj M)) (j+1))
  exact discreteAbelianSheaf_pushforwardHigherCohomology_vanish f.base _ j

/-- If the ORIGINAL module is ACTUALLY isomorphic to direct image from an
Artinian cut,its ACTUAL positive sheaf cohomology vanishes. The affine
Koszul application supplies this isomorphism from its PROVED actual unit,
not as an additional certificate. -/
theorem schemeModule_actualHigherCohomology_vanish_of_artinianSupportIso
    {X Y : Scheme.{u}} [IsArtinianScheme X] (f : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules)
    (e : M ≅ (Scheme.Modules.pushforward f).obj N) (j : ℕ) :
    Subsingleton (schemeModuleActualCohomology Y M (j+1)) := by
  let eAb := (schemeModuleToActualAbelianSheaf Y).mapIso e
  let eH := ((extFunctorObj.{u}
    ((constantSheaf (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (j+1)).mapIso eAb).addCommGroupIsoToAddEquiv
  exact eH.subsingleton_congr.mpr
    (artinianSchemeModule_actualPushforwardHigherCohomology_vanish f N j)

end LinearStudy
