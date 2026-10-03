module

public import Negativity.ActualRelativeReesScheme
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

namespace Negativity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem actual_relative_rees_scheme_locally_of_finite_presentation
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (I : Ideal R) :
    LocallyOfFinitePresentation (actualRelativeReesToBase f I) := by
  letI : IsProper (actualRelativeReesToBase f I) := actual_relative_rees_scheme_proper f I
  infer_instance

theorem actual_relative_rees_scheme_noetherian
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (I : Ideal R) :
    IsNoetherian (actualRelativeReesScheme f I) := by
  letI : IsProper (actualRelativeReesToBase f I) := actual_relative_rees_scheme_proper f I
  letI : IsLocallyNoetherian (actualRelativeReesScheme f I) :=
    LocallyOfFiniteType.isLocallyNoetherian (actualRelativeReesToBase f I)
  letI : CompactSpace (actualRelativeReesScheme f I) :=
    QuasiCompact.compactSpace_of_compactSpace (actualRelativeReesToBase f I)
  exact {}

theorem actual_relative_rees_scheme_separated
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] (I : Ideal R) :
    (actualRelativeReesScheme f I).IsSeparated := by
  letI : IsProper (actualRelativeReesToBase f I) := actual_relative_rees_scheme_proper f I
  constructor
  rw [← terminal.comp_from (actualRelativeReesToBase f I)]
  infer_instance

end
end Negativity
