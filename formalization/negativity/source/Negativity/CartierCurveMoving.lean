module

public import Negativity.CartierCurveRestriction
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Change a Cartier representative by a single actual global rational
function. Local transition units are unchanged. -/
noncomputable def CartierAtlas.rationalTwist {X : Scheme} [IsIntegral X]
    {ι : Type*} (A : CartierAtlas X ι) (a : X.functionFieldˣ) : CartierAtlas X ι where
  chart := A.chart
  affine := A.affine
  nonempty := A.nonempty
  covers := A.covers
  equation := fun i => a * A.equation i
  transition := by
    intro i j x hi hj
    obtain ⟨u, hu⟩ := A.transition i j x hi hj
    refine ⟨u, ?_⟩
    calc
      _ = a * (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u *
          A.equation i) := by exact mul_left_comm _ _ _
      _ = a * A.equation j := congrArg (fun b => a * b) hu

/-- Every Cartier divisor can be moved off the generic image of an
integral curve by subtracting one of its actual local equations. This
works even when the curve is originally contained in the support. -/
theorem cartierAtlas_move_off_generic_curve {C X : Scheme}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ X)
    {ι : Type*} (A : CartierAtlas X ι) :
    ∃ a : X.functionFieldˣ, f (genericPoint C) ∉ (A.rationalTwist a).vanishingSupport := by
  let i := (A.covers (f (genericPoint C))).choose
  let a := (A.equation i)⁻¹
  refine ⟨a, ?_⟩
  have hi : f (genericPoint C) ∈ (A.rationalTwist a).chart i :=
    (A.covers (f (genericPoint C))).choose_spec
  rw [cartierAtlas_support_eq_on_chart X (A.rationalTwist a) i _ hi]
  intro h
  apply h
  refine ⟨1, ?_⟩
  simp [CartierAtlas.rationalTwist, a]

/-- Actual local transition units survive the move unchanged. Thus
moving is a change of divisor representative, not a new numerical input. -/
theorem cartierAtlas_rationalTwist_transition {X : Scheme} [IsIntegral X]
    {ι : Type*} (A : CartierAtlas X ι) (a : X.functionFieldˣ) (i j : ι)
    (x : X) (u : (X.presheaf.stalk x)ˣ)
    (hu : Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u *
      A.equation i = A.equation j) :
    Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u *
      (A.rationalTwist a).equation i = (A.rationalTwist a).equation j := by
  change _ * (a * _) = a * _
  calc
    _ = a * (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u *
        A.equation i) := by exact mul_left_comm _ _ _
    _ = _ := congrArg (fun b => a * b) hu

/-- Construct restriction data for every Cartier divisor on every
integral source by first moving off its generic image. Only the final
independence of the degree under the rational move requires the global
principal-degree theorem for the actual complete curve. -/
theorem exists_moved_cartier_curve_restriction {C X : Scheme}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ X)
    {ι : Type*} (A : CartierAtlas X ι) :
    ∃ (a : X.functionFieldˣ) (B : CartierAtlas C C),
      f (genericPoint C) ∉ (A.rationalTwist a).vanishingSupport ∧
      ∀ z : C, z ∈ B.chart z ∧
        B.chart z ≤ f ⁻¹ᵁ (A.rationalTwist a).chart (A.covers (f z)).choose ∧
        ∃ u : (X.presheaf.stalk (f (genericPoint C)))ˣ,
          Units.map (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom u =
            a * A.equation (A.covers (f z)).choose ∧
          B.equation z = Units.map (f.stalkMap (genericPoint C)).hom.toMonoidHom u := by
  obtain ⟨a, ha⟩ := cartierAtlas_move_off_generic_curve f A
  obtain ⟨B, hB⟩ := exists_cartierAtlas_nondominant_pullback f (A.rationalTwist a) ha
  exact ⟨a, B, ha, hB⟩

end Negativity
