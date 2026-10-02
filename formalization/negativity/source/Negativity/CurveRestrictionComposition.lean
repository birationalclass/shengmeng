module

public import Negativity.CurveIntersectionDegree
public import Negativity.CurveIntersectionPullback
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem dominant_curve_generic_unit_comp
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (p : C ⟶ Y) [IsDominant p] (j : Y ⟶ X)
    (u : (X.presheaf.stalk (j (genericPoint Y)))ˣ) :
    Units.map (dominantFunctionFieldMap p).toMonoidHom
      (Units.map (j.stalkMap (genericPoint Y)).hom.toMonoidHom u) =
    Units.map ((p ≫ j).stalkMap (genericPoint C)).hom.toMonoidHom
      (Units.map (X.presheaf.stalkCongr
        (.of_eq (congrArg j (dominant_genericPoint_eq p)))).inv.hom.toMonoidHom u) := by
  apply Units.ext
  change (((j.stalkMap (genericPoint Y) ≫
    (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq p))).inv) ≫
      p.stalkMap (genericPoint C)) u) = _
  rw [TopCat.Presheaf.stalkCongr_inv]
  change (((j.stalkMap (genericPoint Y) ≫ Y.presheaf.stalkSpecializes
    (Inseparable.of_eq (dominant_genericPoint_eq p)).le) ≫ p.stalkMap (genericPoint C)) u) = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap]
  rw [Scheme.Hom.stalkMap_comp]
  rfl

theorem generic_unit_transport_functionField
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (p : C ⟶ Y) [IsDominant p] (j : Y ⟶ X)
    (u : (X.presheaf.stalk (j (genericPoint Y)))ˣ) :
    Units.map (algebraMap (X.presheaf.stalk (j (p (genericPoint C)))) X.functionField).toMonoidHom
      (Units.map (X.presheaf.stalkCongr
        (.of_eq (congrArg j (dominant_genericPoint_eq p)))).inv.hom.toMonoidHom u) =
    Units.map (algebraMap (X.presheaf.stalk (j (genericPoint Y))) X.functionField).toMonoidHom u := by
  apply Units.ext
  change algebraMap (X.presheaf.stalk (j (p (genericPoint C)))) X.functionField
    ((X.presheaf.stalkCongr (.of_eq (congrArg j (dominant_genericPoint_eq p)))).inv u) = _
  rw [TopCat.Presheaf.stalkCongr_inv]
  exact stalkSpecialization_functionField X _ _ _ (u : X.presheaf.stalk (j (genericPoint Y)))

/-- Final theorem: actual Cartier intersection scales by the full degree
when a complete normal curve is reparametrized by a proper dominant map.
The ambient curve map may be nondominant and the divisor may contain the
curve. Genuine restrictions are compared using actual stalk units. -/
theorem complete_normal_curve_cartier_intersection_reparametrization
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian Y]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdC : Order.krullDim C = 1) (hdY : Order.krullDim Y = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [IsProper b]
    (p : C ⟶ Y) [IsProper p] [IsDominant p] (j : Y ⟶ X)
    {ι : Type*} (A : CartierAtlas X ι) :
    letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (p ≫ b)
    letI : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap p).toAlgebra
    cartierCurveIntersection hnC (p ≫ j) A =
      (Module.finrank Y.functionField C.functionField : ℤ) * cartierCurveIntersection hnY j A := by
  classical
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace b
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (p ≫ b)
  let : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap p).toAlgebra
  let R := movedCartierCurveRestriction j A
  have hη : (p ≫ j) (genericPoint C) ∉ (A.rationalTwist R.move).vanishingSupport := by
    rw [Scheme.Hom.comp_apply, dominant_genericPoint_eq p]
    exact R.avoids
  obtain ⟨B, hB⟩ := exists_cartierAtlas_nondominant_pullback (p ≫ j) (A.rationalTwist R.move) hη
  have hdata : MovedCartierRestrictionData (p ≫ j) A R.move B := hB
  obtain ⟨P, hP, hdeg⟩ := complete_normal_curve_cartier_pullback_degree
    p k b hnC hnY hdC hdY R.atlas
  have hc (x : C) : P.coefficient hnC x = B.coefficient hnC x := by
    by_cases hx : Order.coheight x = 1
    · let y := (R.atlas.covers (p x)).choose
      have hy : j (p x) ∈ A.chart (A.covers (j y)).choose :=
        (R.data y).2.1 (R.atlas.covers (p x)).choose_spec
      obtain ⟨u, v, hu, hv⟩ := moved_restriction_equation_on_chart
        (p ≫ j) A R.move B hdata x _ hy
      obtain ⟨w, hw, hRw⟩ := (R.data y).2.2
      let w' := Units.map (X.presheaf.stalkCongr
        (.of_eq (congrArg j (dominant_genericPoint_eq p)))).inv.hom.toMonoidHom w
      have hw' : Units.map
          (algebraMap (X.presheaf.stalk ((p ≫ j) (genericPoint C))) X.functionField).toMonoidHom w' =
            R.move * A.equation (A.covers (j y)).choose :=
        (generic_unit_transport_functionField p j w).trans hw
      have huw : u = w' := Units.map_injective
        (f := (algebraMap (X.presheaf.stalk ((p ≫ j) (genericPoint C))) X.functionField).toMonoidHom)
        (IsFractionRing.injective _ _) (hu.trans hw'.symm)
      have he : P.equation x =
          Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom v * B.equation x := by
        rw [(hP x).2.2, hRw, dominant_curve_generic_unit_comp]
        change Units.map ((p ≫ j).stalkMap (genericPoint C)).hom.toMonoidHom w' = _
        exact (congrArg (Units.map ((p ≫ j).stalkMap (genericPoint C)).hom.toMonoidHom) huw.symm).trans hv
      rw [cartierAtlas_coefficient_eq C hnC P x x hx (hP x).2.1,
        cartierAtlas_coefficient_eq C hnC B x x hx (hB x).1, he]
      have := hnC x
      have := normal_codimensionOne_stalk_isDVR C x hx
      exact dvr_rationalOrder_unit_transition (C.presheaf.stalk x) C.functionField v _
    · simp [CartierAtlas.coefficient, hx]
  have heq : cartierOrderDivisor C hnC B = cartierOrderDivisor C hnC P := by
    ext x
    simpa only [cartierOrderDivisor_apply] using (hc x).symm
  rw [complete_normal_curve_cartier_intersection_eq_restriction hnC hdC k (p ≫ b)
    (p ≫ j) A R.move B hdata]
  change (cartierOrderDivisor C hnC B).degree = _
  rw [heq]
  exact hdeg

end
end Negativity
