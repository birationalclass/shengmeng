module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: an actual closed-point fiber of an actual proper map
over a field is proper over that same field. Finiteness of the residue
point over the ground field is derived from finite type and Jacobsonness.
No rational-point identification or fiber completeness is supplied. -/
theorem actual_closed_fiber_proper_over_ground_field
    {X Y : Scheme.{u}} (k : Type u) [Field k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (y : Y) (hy : IsClosed ({y} : Set Y)) :
    IsProper (f.fiberι y ≫ f ≫ b) := by
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsFinite (Y.fromSpecResidueField y ≫ b) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have : IsProper (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsProper f)
  have h : IsProper (f.fiberToSpecResidueField y ≫ (Y.fromSpecResidueField y ≫ b)) :=
    inferInstance
  simpa only [← Category.assoc, Scheme.Hom.fiber_fac] using h

end
end Negativity
