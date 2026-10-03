module

public import Negativity.ProperBirationalStructureSheaf
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Every actual open component of the proved structure-sheaf isomorphism
is an isomorphism. Neither affineness nor a chosen descent map is assumed. -/
theorem proper_normal_birational_open_functions_isIso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) : IsIso (f.app U) := by
  have : IsIso (actualStructureSheafPullback f) :=
    proper_normal_birational_structure_sheaf_isIso f hf hnY
  have : IsIso ((TopCat.Sheaf.forget CommRingCat Y.carrier).map
    (actualStructureSheafPullback f)) := inferInstance
  change IsIso f.c at this
  change IsIso (f.c.app (op U))
  infer_instance

/-- Final theorem: regular functions descend uniquely on every actual
base open of a proper birational map to a normal locally Noetherian
integral scheme, including nonaffine and empty opens. The descent is the
actual pullback map, not an abstract ring comparison supplied as input. -/
theorem proper_normal_birational_open_functions_bijective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) : Function.Bijective (f.app U) := by
  have : IsIso (f.app U) :=
    proper_normal_birational_open_functions_isIso f hf hnY U
  exact ConcreteCategory.bijective_of_isIso (f.app U)

end
end Negativity
