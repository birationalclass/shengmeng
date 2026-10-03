module

public import Mathlib
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false


/-!
# Finite-stage models of proper affine-intersection diagrams

A proper, locally finitely presented scheme over an affine base admits a finite
affine cover whose complete intersection diagram consists of finitely presented
base algebras. The diagram can therefore be spread to one stage of any filtered
presentation of the base ring while retaining the geometric gluing conditions.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} {J : Type u}

/-- A separated, locally finite-type morphism is proper if it has a surjective
cover whose composite to the target is proper. -/
lemma IsProper.of_comp_surjective {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper (f ≫ g)] [Surjective f] [IsSeparated g] [LocallyOfFiniteType g] :
    IsProper g where
  toIsSeparated := inferInstance
  toUniversallyClosed := UniversallyClosed.of_comp_surjective f g
  toLocallyOfFiniteType := inferInstance

/-- A proper open immersion is also a closed immersion. -/
lemma IsClosedImmersion.of_isOpenImmersion_isProper (f : X ⟶ S)
    [IsOpenImmersion f] [IsProper f] : IsClosedImmersion f := by
  apply IsClosedImmersion.of_isPreimmersion f
  rw [← Set.image_univ]
  exact f.isProperMap.isClosedMap _ isClosed_univ

/-- An open immersion into a separated family is closed when its composite to the base
is proper. -/
lemma IsClosedImmersion.of_isOpenImmersion_comp_isProper
    {Y : Scheme.{u}} (f : X ⟶ S) (g : S ⟶ Y) [IsOpenImmersion f]
    [IsProper (f ≫ g)] [IsSeparated g] : IsClosedImmersion f := by
  letI : IsProper f := IsProper.of_comp f g
  exact IsClosedImmersion.of_isOpenImmersion_isProper f


end
end AlgebraicGeometry
