module

public import Negativity.CurveCartierCombinations
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Repeat the actual affine Cartier charts using ambient points as
indices. This changes the presentation, not the local Cartier divisor. -/
def CartierAtlas.pointIndexed {X : Scheme} [IsIntegral X] {ι : Type*}
    (A : CartierAtlas X ι) : CartierAtlas X X where
  chart x := A.chart (A.covers x).choose
  affine _x := A.affine _
  nonempty _x := A.nonempty _
  covers x := ⟨x, (A.covers x).choose_spec⟩
  equation x := A.equation (A.covers x).choose
  transition _i _j x hi hj := A.transition _ _ x hi hj

theorem cartierAtlas_pointIndexed_coefficient {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X]
    (hn : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {ι : Type*} (A : CartierAtlas X ι) (x : X) :
    A.pointIndexed.coefficient hn x = A.coefficient hn x := by
  classical
  by_cases hx : Order.coheight x = 1
  · rw [cartierAtlas_coefficient_eq X hn A.pointIndexed x x hx (A.covers x).choose_spec,
      cartierAtlas_coefficient_eq X hn A _ x hx (A.covers x).choose_spec]
    rfl
  · simp [CartierAtlas.coefficient, hx]

/-- Final theorem: repeating an actual Cartier affine cover has no effect
on its constructed complete-curve intersection. All discrepancies between
the two actual source restrictions are genuine source-stalk units. -/
theorem complete_normal_curve_cartier_intersection_pointIndexed
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    cartierCurveIntersection hn f A.pointIndexed = cartierCurveIntersection hn f A := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let R := movedCartierCurveRestriction f A
  let a := R.move
  let B := R.atlas
  have hB : MovedCartierRestrictionData f A a B := R.data
  have hη : f (genericPoint C) ∉ (A.pointIndexed.rationalTwist a).vanishingSupport := by
    rw [cartierAtlas_support_eq_on_chart X (A.pointIndexed.rationalTwist a)
      (f (genericPoint C)) _ (A.covers (f (genericPoint C))).choose_spec]
    obtain ⟨u, hu, _⟩ := (hB (genericPoint C)).2.2
    exact fun h => h ⟨u, hu⟩
  obtain ⟨E, hE⟩ := exists_cartierAtlas_nondominant_pullback f (A.pointIndexed.rationalTwist a) hη
  have hdata : MovedCartierRestrictionData f A.pointIndexed a E := hE
  have hc (x : C) : E.coefficient hn x = B.coefficient hn x := by
    by_cases hx : Order.coheight x = 1
    · let j := (A.pointIndexed.covers (f x)).choose
      have hj : f x ∈ A.chart (A.covers j).choose := (A.pointIndexed.covers (f x)).choose_spec
      obtain ⟨u, v, hu, hv⟩ := moved_restriction_equation_on_chart f A a B hB x _ hj
      obtain ⟨uE, huE, hEuE⟩ := (hE x).2.2
      have hue : uE = u := by
        apply Units.map_injective
          (f := (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom)
          (IsFractionRing.injective _ _)
        exact huE.trans hu.symm
      have he : E.equation x =
          Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom v * B.equation x := by
        rw [hEuE, hue]
        exact hv
      rw [cartierAtlas_coefficient_eq C hn E x x hx (hE x).1,
        cartierAtlas_coefficient_eq C hn B x x hx (hB x).1, he]
      have := hn x
      have := normal_codimensionOne_stalk_isDVR C x hx
      exact dvr_rationalOrder_unit_transition (C.presheaf.stalk x) C.functionField v _
    · simp [CartierAtlas.coefficient, hx]
  have heq : cartierOrderDivisor C hn E = cartierOrderDivisor C hn B := by
    ext x
    simpa only [cartierOrderDivisor_apply] using hc x
  rw [complete_normal_curve_cartier_intersection_eq_restriction hn hd k c f
      A.pointIndexed a E hdata,
    complete_normal_curve_cartier_intersection_eq_restriction hn hd k c f A a B hB]
  change (cartierOrderDivisor C hn E).degree = (cartierOrderDivisor C hn B).degree
  rw [heq]

end
end Negativity
