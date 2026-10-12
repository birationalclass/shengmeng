module
public import Linear.SchemeModuleAdditiveSheafColimits
public import Linear.SheafCohomologySectionSurjectivity
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u w

/-- For an ACTUAL short exact sequence of O_X-module sheaves, H1 vanishing
of its ACTUAL underlying additive sheaf gives a lift of every global section.
The exact additive comparison is DERIVED; no comparison certificate or
polynomial-lifting hypothesis is assumed. Eventual Serre vanishing remains
separate, as does the original canonical identification. -/
theorem schemeModuleShortExact_sections_surjective_of_H1_vanish
    {X : Scheme.{u}} [HasExt.{w} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{w}
      ((schemeModuleToAdditiveSheaf X).obj S.X₁) 1)] :
    Function.Surjective (S.g.app ⊤) := by
  letI : (schemeModuleToAdditiveSheaf X).PreservesZeroMorphisms :=
    schemeModuleAdditiveSheaf_preservesZeroMorphisms X
  change Function.Surjective
    ((S.map (schemeModuleToAdditiveSheaf X)).g.hom.app (op ⊤))
  letI : Subsingleton (CategoryTheory.Sheaf.H.{w}
      (S.map (schemeModuleToAdditiveSheaf X)).X₁ 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H.{w}
      ((schemeModuleToAdditiveSheaf X).obj S.X₁) 1)
    infer_instance
  exact sheafShortExact_sections_surjective_of_H1_vanish
    (S.map (schemeModuleToAdditiveSheaf X))
    (schemeModuleShortExact_underlyingAdditiveSheaf S hS) isTerminalTop
end LinearStudy
