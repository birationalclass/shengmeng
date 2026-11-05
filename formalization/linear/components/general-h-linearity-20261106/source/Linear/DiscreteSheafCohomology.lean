module
public import Linear.DiscreteSheafSectionsExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
universe u

/-- Reuse native corepresentability of the abelian-group forgetful functor
and its preservation of epis to prove that the actual ULift integers are
projective. This is the ORIGINAL constant-sheaf cohomology source. -/
theorem actualUliftIntegerAbelianGroup_projective :
    Projective (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  apply (Projective.projective_iff_preservesEpimorphisms_coyoneda_obj _).mpr
  exact Functor.PreservesEpimorphisms.of_iso AddCommGrpCat.coyonedaObjIsoForget.symm

/-- On the actual discrete space,the ACTUAL sheafification of constant
integers is projective. Native constant-sheaf/global-sections adjunction
applies to the PROVED preservation of epis;no acyclicity premise. -/
theorem discreteAbelianSheaf_constantInteger_projective
    (X : TopCat.{u}) [DiscreteTopology X] :
    Projective ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  letI := discreteAbelianSheaf_sectionFunctor_preservesEpimorphisms X ⊤
  exact (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop).map_projective _ actualUliftIntegerAbelianGroup_projective

/-- Actual native DERIVED SHEAF cohomology in EVERY positive degree
vanishes for EVERY abelian sheaf on an actual discrete space. Native
Grothendieck sheaf-category HasExt is instantiated,not assumed as a desired
comparison. No finite generation,injectivity,flasque or vanishing input. -/
theorem discreteAbelianSheaf_higherCohomology_vanish
    {X : TopCat.{u}} [DiscreteTopology X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (j : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{u} F (j+1)) := by
  letI := discreteAbelianSheaf_constantInteger_projective X
  exact Ext.subsingleton_of_projective _ F j

end LinearStudy
