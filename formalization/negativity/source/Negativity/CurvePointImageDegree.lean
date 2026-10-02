module

public import Negativity.CartierCurveMoving
public import Negativity.ProperCurveCartierDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual Cartier equations identically one give zero stalk coefficients
and zero total order; there is no assumed degree-zero input. -/
theorem cartierTotalOrder_zero_of_equations_one (C : Scheme) [IsIntegral C]
    [IsLocallyNoetherian C] [CompactSpace C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    {ι : Type*} (B : CartierAtlas C ι) (hB : ∀ i, B.equation i = 1) :
    cartierTotalOrder C hn B = 0 := by
  classical
  have hc (x : C) : B.coefficient hn x = 0 := by
    by_cases hx : Order.coheight x = 1
    · rw [cartierAtlas_coefficient_eq C hn B _ x hx (B.covers x).choose_spec, hB]
      have := hn x
      have := normal_codimensionOne_stalk_isDVR C x hx
      unfold schemeRationalOrder
      simpa only [map_one] using dvr_rationalOrder_unit (C.presheaf.stalk x) C.functionField
        (1 : (C.presheaf.stalk x)ˣ)
    · simp [CartierAtlas.coefficient, hx]
  unfold cartierTotalOrder Finsupp.sum
  apply Finset.sum_eq_zero
  intro x _
  exact hc x

/-- Final theorem: for an actual morphism whose actual point image is a
single point, divide by the Cartier equation of a chart at that point.
The moved Cartier restriction is genuinely constructed using stalk maps;
all of its actual local equations are one and its total order is zero.
Independence from the choice of move is a separate next theorem. -/
theorem constant_image_moved_cartier_restriction_degree_zero
    {C X : Scheme} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [CompactSpace C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (f : C ⟶ X) (hf : ∀ x : C, f x = f (genericPoint C))
    {ι : Type*} (A : CartierAtlas X ι) :
    ∃ (a : X.functionFieldˣ) (B : CartierAtlas C C),
      f (genericPoint C) ∉ (A.rationalTwist a).vanishingSupport ∧
      (∀ z : C, z ∈ B.chart z ∧
        B.chart z ≤ f ⁻¹ᵁ (A.rationalTwist a).chart (A.covers (f z)).choose ∧
        ∃ u : (X.presheaf.stalk (f (genericPoint C)))ˣ,
          Units.map (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom u =
            a * A.equation (A.covers (f z)).choose ∧
          B.equation z = Units.map (f.stalkMap (genericPoint C)).hom.toMonoidHom u) ∧
      (∀ z, B.equation z = 1) ∧ cartierTotalOrder C hn B = 0 := by
  classical
  let i := (A.covers (f (genericPoint C))).choose
  let a := (A.equation i)⁻¹
  have hη : f (genericPoint C) ∉ (A.rationalTwist a).vanishingSupport := by
    rw [cartierAtlas_support_eq_on_chart X (A.rationalTwist a) i _
      (A.covers (f (genericPoint C))).choose_spec]
    intro h
    apply h
    refine ⟨1, ?_⟩
    simp [CartierAtlas.rationalTwist, a]
  obtain ⟨B, hB⟩ := exists_cartierAtlas_nondominant_pullback f (A.rationalTwist a) hη
  have he (z : C) : B.equation z = 1 := by
    obtain ⟨u, hu, hBu⟩ := (hB z).2.2
    have hu1 : Units.map (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom u = 1 := by
      rw [hu]
      simp [CartierAtlas.rationalTwist, hf z, a, i]
    have huone : u = 1 := by
      apply Units.ext
      apply IsFractionRing.injective (X.presheaf.stalk (f (genericPoint C))) X.functionField
      have hv := congrArg Units.val hu1
      change algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField (u : _) = 1 at hv
      simpa only [Units.val_one, map_one] using hv
    rw [hBu, huone, map_one]
  refine ⟨a, B, hη, ?_, he, cartierTotalOrder_zero_of_equations_one C hn B he⟩
  intro z
  exact hB z

end
end Negativity
