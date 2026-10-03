module
public import Negativity.ActualAffineOpenReesRestrictionFinal
public import Negativity.ActualReesCechDifferentialsFromNaturality

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The actual coordinate restriction premise used in the Čech construction
is proved from the genuine scheme maps. It is not supplied as an input. -/
theorem actual_rees_coordinate_restriction_compatibility
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R) :
    ActualReesCoordinateRestrictionCompatibility f I := by
  intro U V hU hV h a n
  exact actual_affine_open_rees_sections_restriction_coeff f I h hU hV a n

#print axioms actual_rees_coordinate_restriction_compatibility
end
end Negativity
