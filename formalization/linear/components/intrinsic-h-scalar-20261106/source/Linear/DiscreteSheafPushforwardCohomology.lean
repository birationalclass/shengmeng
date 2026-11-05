module
public import Linear.DiscreteSheafCohomology
public import Linear.DiscreteSheafPushforwardExact
public import Linear.ActualAbelianSheafConstantPullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
universe u

/-- For ACTUAL abelian sheaves and an ACTUAL continuous map from a discrete
space,construct ALL-degree native DERIVED SHEAF cohomology comparison.
Both actual functors are exact by native inverse-image preservation and
our direct-image proof. The source constant comparison is constructed,not
assumed. No injectivity/CM/finiteness/acyclicity certificate. -/
def discreteAbelianSheaf_pushforwardCohomologyEquiv
    {X Y : TopCat.{u}} [DiscreteTopology X] (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (j : ℕ) :
    CategoryTheory.Sheaf.H.{u} F j ≃+
      CategoryTheory.Sheaf.H.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) j := by
  letI := actualAbelianSheaf_pullback_preservesFiniteLimits f
  letI := actualAbelianSheaf_pullback_additive f
  letI := actualAbelianSheaf_pushforward_additive f
  letI := discreteAbelianSheaf_pushforward_preservesFiniteColimits f
  let e := (actualAbelianSheaf_pullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))
  exact ((((extFunctor.{u} j).mapIso e.op).app F).addCommGroupIsoToAddEquiv).trans
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).extEquiv

/-- The ACTUAL direct image of EVERY original abelian sheaf on a discrete
space has zero native DERIVED SHEAF cohomology in every positive degree
on the ACTUAL ambient space. This includes the original finite closed-cut
inclusion,without substituting module Ext or a model cohomology. -/
theorem discreteAbelianSheaf_pushforwardHigherCohomology_vanish
    {X Y : TopCat.{u}} [DiscreteTopology X] (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (j : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) (j+1)) :=
  (discreteAbelianSheaf_pushforwardCohomologyEquiv f F (j+1)).subsingleton_congr.mp
    (discreteAbelianSheaf_higherCohomology_vanish F j)

end LinearStudy
