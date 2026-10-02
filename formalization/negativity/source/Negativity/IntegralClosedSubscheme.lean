module

public import Negativity.CompleteCurveThroughPoint
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem vanishingIdeal_subscheme_isReduced
    (X : Scheme.{u}) (F : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal F).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal F
  have hred : ∀ U : X.affineOpens, IsReduced (I.glueDataObj U) := by
    intro U
    have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) := by
      apply (Ideal.isRadical_iff_quotient_reduced _).mp
      change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' F)).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    exact inferInstanceAs (IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U))))
  let : ∀ U, IsReduced (I.subschemeCover.openCover.X U) := hred
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

/-- Final theorem: every actual closed irreducible subset has a constructed
reduced integral closed subscheme structure, including inside a nonreduced
or reducible ambient fiber. -/
theorem closed_irreducible_actual_subscheme_properties
    (X : Scheme.{u}) (F : Closeds X) (hF : IsIrreducible (F : Set X)) :
    let I := Scheme.IdealSheafData.vanishingIdeal F
    IsIntegral I.subscheme ∧ IsClosedImmersion I.subschemeι ∧
      Set.range I.subschemeι = F := by
  let I := Scheme.IdealSheafData.vanishingIdeal F
  have : IsReduced I.subscheme := vanishingIdeal_subscheme_isReduced X F
  have : IrreducibleSpace I.subscheme := by
    exact Subtype.irreducibleSpace hF
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  exact ⟨inferInstance, inferInstance, by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl⟩

end
end Negativity
