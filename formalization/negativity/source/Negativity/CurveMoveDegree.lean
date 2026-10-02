module

public import Negativity.CartierCurveMoving
public import Negativity.CartierDegreeInvariance
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Data produced by the actual nondominant stalk pullback after moving
an ambient Cartier representative. No order or degree identity is input. -/
def MovedCartierRestrictionData {C X : Scheme} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι)
    (a : X.functionFieldˣ) (B : CartierAtlas C C) : Prop :=
  ∀ z : C, z ∈ B.chart z ∧
    B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧
    ∃ u : (X.presheaf.stalk (f (genericPoint C)))ˣ,
      Units.map (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom u =
        a * A.equation (A.covers (f z)).choose ∧
      B.equation z = Units.map (f.stalkMap (genericPoint C)).hom.toMonoidHom u

/-- The ratio of two moves that genuinely restrict is a unit at the
generic image, even if either ambient move separately cannot be pulled
back as a rational function. Its actual stalk pullback is one global
rational unit relating all source equations. -/
theorem moved_cartier_restriction_ratio_equations
    {C X : Scheme} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι)
    (a b : X.functionFieldˣ) (B₁ B₂ : CartierAtlas C C)
    (h₁ : MovedCartierRestrictionData f A a B₁)
    (h₂ : MovedCartierRestrictionData f A b B₂) :
    ∃ r : C.functionFieldˣ, ∀ z : C, B₂.equation z = r * B₁.equation z := by
  classical
  let η := genericPoint C
  let e := (algebraMap (X.presheaf.stalk (f η)) X.functionField).toMonoidHom
  let p := (f.stalkMap η).hom.toMonoidHom
  obtain ⟨u₀, hu₀, _⟩ := (h₁ η).2.2
  obtain ⟨v₀, hv₀, _⟩ := (h₂ η).2.2
  let w := v₀ * u₀⁻¹
  have hw : Units.map e w = b * a⁻¹ := by
    change Units.map e (v₀ * u₀⁻¹) = _
    rw [map_mul, map_inv, hv₀, hu₀]
    group
  refine ⟨Units.map p w, fun z => ?_⟩
  obtain ⟨u, hu, hBu⟩ := (h₁ z).2.2
  obtain ⟨v, hv, hBv⟩ := (h₂ z).2.2
  have huv : w * u = v := by
    apply Units.map_injective (f := e)
      (IsFractionRing.injective (X.presheaf.stalk (f η)) X.functionField)
    rw [map_mul, hw, hu, hv]
    group
  rw [hBv, hBu, ← map_mul, huv]

/-- Final theorem: on an actual complete normal curve over an algebraically
closed field of arbitrary characteristic, every two genuine moved Cartier
restrictions have equal total order. Principal degree zero is derived from
the curve hypotheses; neither degree invariance nor the ratio is assumed. -/
theorem complete_normal_curve_moved_restriction_degree_independent
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι)
    (a b : X.functionFieldˣ) (B₁ B₂ : CartierAtlas C C)
    (h₁ : MovedCartierRestrictionData f A a B₁)
    (h₂ : MovedCartierRestrictionData f A b B₂) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    cartierTotalOrder C hn B₂ = cartierTotalOrder C hn B₁ := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  let : Algebra k C.functionField := (curveFunctionFieldBaseMap C k c).toAlgebra
  obtain ⟨r, hr⟩ := moved_cartier_restriction_ratio_equations f A a b B₁ B₂ h₁ h₂
  have he : cartierOrderDivisor C hn B₂ =
      cartierOrderDivisor C hn (B₁.rationalTwist r) := by
    ext x
    rw [cartierOrderDivisor_apply, cartierOrderDivisor_apply]
    by_cases hx : Order.coheight x = 1
    · rw [cartierAtlas_coefficient_eq C hn B₂ x x hx (h₂ x).1,
        cartierAtlas_coefficient_eq C hn (B₁.rationalTwist r) x x hx (h₁ x).1]
      exact congrArg (schemeRationalOrder C hn x hx) (hr x)
    · simp [CartierAtlas.coefficient, hx]
  change (cartierOrderDivisor C hn B₂).degree = (cartierOrderDivisor C hn B₁).degree
  rw [he]
  exact complete_normal_curve_cartier_degree_invariant C hn hd k c rfl B₁ r

end
end Negativity
