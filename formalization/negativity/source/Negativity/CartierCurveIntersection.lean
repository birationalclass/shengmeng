module

public import Negativity.CurveMoveDegree
public import Negativity.CurvePointImageDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- One actual moved restriction, including the local stalk pullback data.
No numerical intersection or degree compatibility is supplied. -/
structure MovedCartierCurveRestriction {C X : Scheme} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) where
  move : X.functionFieldˣ
  atlas : CartierAtlas C C
  avoids : f (genericPoint C) ∉ (A.rationalTwist move).vanishingSupport
  data : MovedCartierRestrictionData f A move atlas

/-- Construct a restriction for any Cartier divisor, including when the
curve lies in its support, from actual rational equations and stalk maps. -/
def movedCartierCurveRestriction {C X : Scheme} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) :
    MovedCartierCurveRestriction f A := by
  apply Classical.choice
  obtain ⟨a, B, ha, hB⟩ := exists_moved_cartier_curve_restriction f A
  exact ⟨⟨a, B, ha, hB⟩⟩

/-- Cartier intersection with an actual complete normal curve is the sum
of the local orders of its constructed restriction. The complete-curve
result below proves that the construction choices do not affect it. -/
def cartierCurveIntersection {C X : Scheme} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [CompactSpace C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) : ℤ :=
  cartierTotalOrder C hn (movedCartierCurveRestriction f A).atlas

theorem complete_normal_curve_cartier_intersection_eq_restriction
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι)
    (a : X.functionFieldˣ) (B : CartierAtlas C C)
    (hB : MovedCartierRestrictionData f A a B) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    cartierCurveIntersection hn f A = cartierTotalOrder C hn B := by
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  exact complete_normal_curve_moved_restriction_degree_independent hn hd k c f A
    a (movedCartierCurveRestriction f A).move B
    (movedCartierCurveRestriction f A).atlas hB (movedCartierCurveRestriction f A).data

/-- Final theorem: the actual local-order definition of Cartier intersection
on a complete normal curve is independent of every permitted rational move
and affine-chart choice. If the actual morphism contracts the curve to a
point, this well-defined intersection is zero. Both conclusions hold over
an algebraically closed base field of arbitrary characteristic. -/
theorem complete_normal_curve_cartier_intersection_wellDefined
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    (∀ (a : X.functionFieldˣ) (B : CartierAtlas C C),
      MovedCartierRestrictionData f A a B →
      cartierCurveIntersection hn f A = cartierTotalOrder C hn B) ∧
    ((∀ x : C, f x = f (genericPoint C)) → cartierCurveIntersection hn f A = 0) := by
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  refine ⟨fun a B hB =>
    complete_normal_curve_cartier_intersection_eq_restriction hn hd k c f A a B hB, ?_⟩
  intro hf
  obtain ⟨a, B, _, hB, _, hz⟩ :=
    constant_image_moved_cartier_restriction_degree_zero hn f hf A
  exact (complete_normal_curve_cartier_intersection_eq_restriction hn hd k c f A a B hB).trans hz

end
end Negativity
