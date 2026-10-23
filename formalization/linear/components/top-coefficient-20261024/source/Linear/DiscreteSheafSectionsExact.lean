module
public import Linear.DiscreteSheafFlasque
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u

/-- Every actual epi of abelian sheaves on a discrete space is onto on
EVERY original open-section group. Its original kernel is flasque by the
proved zero-extension theorem;the native exact/flasque theorem applies. -/
theorem discreteAbelianSheaf_sections_epi
    {X : TopCat.{u}} [DiscreteTopology X]
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (g : F ⟶ G) [Epi g]
    (U : Opens X) : Epi (g.hom.app (op U)) := by
  letI : TopCat.Sheaf.IsFlasque (ShortComplex.kernelSequence g).X₁ :=
    discreteAbelianSheaf_isFlasque (kernel g)
  letI : Epi (ShortComplex.kernelSequence g).g := (inferInstance : Epi g)
  have hS : (ShortComplex.kernelSequence g).ShortExact :=
    ⟨ShortComplex.kernelSequence_exact g⟩
  exact TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS

/-- The ACTUAL evaluation functor on EVERY original open of a discrete
space preserves epimorphisms;no higher-cohomology vanishing input. -/
theorem discreteAbelianSheaf_sectionFunctor_preservesEpimorphisms
    (X : TopCat.{u}) [DiscreteTopology X] (U : Opens X) :
    ((CategoryTheory.sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (op U)).PreservesEpimorphisms where
  preserves g := discreteAbelianSheaf_sections_epi g U

end LinearStudy
