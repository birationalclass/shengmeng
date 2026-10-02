module

public import Negativity.CartierCurveIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The same actual source restriction is valid for a principally changed
ambient Cartier atlas by changing its ambient move. This does not require
the original principal function to restrict to the curve. -/
theorem movedCartierRestrictionData_rationalTwist
    {C X : Scheme} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι)
    (a b : X.functionFieldˣ) (B : CartierAtlas C C)
    (hB : MovedCartierRestrictionData f A b B) :
    MovedCartierRestrictionData f (A.rationalTwist a) (b * a⁻¹) B := by
  intro z
  obtain ⟨hz, hle, u, hu, hBu⟩ := hB z
  refine ⟨hz, hle, u, ?_, hBu⟩
  change _ = (b * a⁻¹) * (a * A.equation (A.covers (f z)).choose)
  rw [hu]
  group

/-- Final theorem: actual Cartier intersection with a complete normal
curve is unchanged by any principal change of the ambient Cartier atlas.
This remains valid when the curve is contained in the support of the
ambient rational function, so directly pulling that function back would
be invalid. The proof compares two genuine restriction constructions. -/
theorem complete_normal_curve_ambient_cartier_principal_invariance
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) (a : X.functionFieldˣ) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    cartierCurveIntersection hn f (A.rationalTwist a) = cartierCurveIntersection hn f A := by
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let B := movedCartierCurveRestriction f A
  have h₁ := complete_normal_curve_cartier_intersection_eq_restriction
    hn hd k c f A B.move B.atlas B.data
  have h₂ := complete_normal_curve_cartier_intersection_eq_restriction
    hn hd k c f (A.rationalTwist a) (B.move * a⁻¹) B.atlas
      (movedCartierRestrictionData_rationalTwist f A a B.move B.atlas B.data)
  exact h₂.trans h₁.symm

end
end Negativity
