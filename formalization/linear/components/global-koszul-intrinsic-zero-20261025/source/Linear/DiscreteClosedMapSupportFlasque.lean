module
public import Linear.ClosedDiscreteSupportSheafFlasque
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Every open slice of the image of an actual closed map from a discrete space is closed in the ORIGINAL ambient space. -/
theorem discreteClosedMap_range_inter_open_isClosed
    {D X : TopCat.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (V : Opens X) : IsClosed (Set.range f ∩ (V : Set X)) := by
  have h := hf (f ⁻¹' (V : Set X)) (isClosed_discrete _)
  simpa only [Set.image_preimage_eq_inter_range,Set.inter_comm] using h
/-- Actual sheaf flasqueness follows from vanishing off the original closed discrete image, using the actual restriction maps. -/
theorem discreteClosedMap_supportedAbelianSheaf_isFlasque
    {D X : TopCat.{u}} [DiscreteTopology D] (f : D ⟶ X) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hzero : ∀ T : Opens X, Disjoint (T : Set X) (Set.range f) →
      Subsingleton (F.obj.obj (op T))) : TopCat.Sheaf.IsFlasque F :=
  closedDiscreteSupportAbelianSheaf_isFlasque (Set.range f)
    (discreteClosedMap_range_inter_open_isClosed f hf) F hzero
end LinearStudy
