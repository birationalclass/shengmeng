module

public import Negativity.RealCurveIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual generic stalk pullback composes with an arbitrary curve map. -/
theorem curve_generic_stalk_pullback_comp
    {C Y X : Scheme} (g : C ⟶ Y) (p : Y ⟶ X) (x : C)
    (u : (X.presheaf.stalk (p (g x)))ˣ) :
    Units.map (g.stalkMap x).hom.toMonoidHom
      (Units.map (p.stalkMap (g x)).hom.toMonoidHom u) =
        Units.map ((g ≫ p).stalkMap x).hom.toMonoidHom u := by
  apply Units.ext
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- Final theorem: genuine ambient Cartier pullback is compatible with
the constructed actual complete-normal-curve intersection, including
curves contained in the original divisor support. The pullback atlas is
constructed here and no functoriality or numerical identity is input. -/
theorem exists_complete_curve_cartier_intersection_pullback
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (p : Y ⟶ X) [IsDominant p] (g : C ⟶ Y)
    {ι : Type*} (A : CartierAtlas X ι) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    ∃ P : CartierAtlas Y Y,
      (∀ y : Y, P.chart y ≤ p ⁻¹ᵁ A.chart (A.covers (p y)).choose ∧ y ∈ P.chart y ∧
        P.equation y = Units.map (dominantFunctionFieldMap p).toMonoidHom
          (A.equation (A.covers (p y)).choose)) ∧
      cartierCurveIntersection hn g P = cartierCurveIntersection hn (g ≫ p) A := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨P, hP⟩ := exists_cartierAtlas_pullback p A
  let R := movedCartierCurveRestriction (g ≫ p) A
  let a := R.move
  let B := R.atlas
  have hB : MovedCartierRestrictionData (g ≫ p) A a B := R.data
  let b := Units.map (dominantFunctionFieldMap p).toMonoidHom a
  have hη : g (genericPoint C) ∉ (P.rationalTwist b).vanishingSupport := by
    rw [cartierAtlas_support_eq_on_chart Y (P.rationalTwist b)
      (g (genericPoint C)) _ (hP _).2.1]
    intro h
    apply h
    obtain ⟨u, hu, _⟩ := (hB (genericPoint C)).2.2
    refine ⟨Units.map (p.stalkMap (g (genericPoint C))).hom.toMonoidHom u, ?_⟩
    change _ = b * P.equation (g (genericPoint C))
    rw [(hP _).2.2]
    have hs := dominantFunctionFieldMap_stalk_unit p (g (genericPoint C)) u
    exact hs.symm.trans ((congrArg (Units.map (dominantFunctionFieldMap p).toMonoidHom) hu).trans
      (map_mul _ _ _))
  obtain ⟨E, hE⟩ := exists_cartierAtlas_nondominant_pullback g (P.rationalTwist b) hη
  have hdata : MovedCartierRestrictionData g P b E := hE
  have hc (x : C) : E.coefficient hn x = B.coefficient hn x := by
    by_cases hx : Order.coheight x = 1
    · let j := (P.covers (g x)).choose
      have hj : p (g x) ∈ A.chart (A.covers (p j)).choose :=
        (hP j).1 (P.covers (g x)).choose_spec
      obtain ⟨u, v, hu, hv⟩ :=
        moved_restriction_equation_on_chart (g ≫ p) A a B hB x _ hj
      obtain ⟨uE, huE, hEuE⟩ := (hE x).2.2
      have hpu : Units.map
          (algebraMap (Y.presheaf.stalk (g (genericPoint C))) Y.functionField).toMonoidHom
          (Units.map (p.stalkMap (g (genericPoint C))).hom.toMonoidHom u) =
            b * P.equation j := by
        rw [(hP j).2.2]
        have hs := dominantFunctionFieldMap_stalk_unit p (g (genericPoint C)) u
        exact hs.symm.trans ((congrArg (Units.map (dominantFunctionFieldMap p).toMonoidHom) hu).trans
          (map_mul _ _ _))
      have hue : uE = Units.map (p.stalkMap (g (genericPoint C))).hom.toMonoidHom u := by
        apply Units.map_injective
          (f := (algebraMap (Y.presheaf.stalk (g (genericPoint C))) Y.functionField).toMonoidHom)
          (IsFractionRing.injective _ _)
        exact huE.trans hpu.symm
      have he : E.equation x =
          Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom v * B.equation x := by
        rw [hEuE, hue, curve_generic_stalk_pullback_comp]
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
  refine ⟨P, hP, ?_⟩
  rw [complete_normal_curve_cartier_intersection_eq_restriction hn hd k c g P b E hdata,
    complete_normal_curve_cartier_intersection_eq_restriction hn hd k c (g ≫ p) A a B hB]
  change (cartierOrderDivisor C hn E).degree = (cartierOrderDivisor C hn B).degree
  rw [heq]

end
end Negativity
