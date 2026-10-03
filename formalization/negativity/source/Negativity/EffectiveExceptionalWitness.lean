module

public import Negativity.CartierEffectiveTwist
public import Negativity.NormalizedPrincipalInvariance
public import Negativity.ZeroPrimeCurve
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: from a single actual Cartier divisor with strictly
negative degrees on complete contracted curves, construct an effective
principal twist with positive coefficients at every actual exceptional
prime. Effectivity and exceptional coverage are outputs, not assumptions.
Geometric relative ampleness and its positive-degree theorem are not
asserted here; the precise numerical strict negativity is explicit. -/
theorem exists_effective_exceptional_covering_cartier_twist
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [CompactSpace X]
    [IsLocallyNoetherian X] [IsAffine Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {ι : Type*} (A : CartierAtlas X ι)
    (hanti : ∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
      (j : C ⟶ X) [IsProper (j ≫ f ≫ b)], IsClosedImmersion j →
      (∀ c : C, f (j c) = f (j (genericPoint C))) →
      normalizedCartierCurveIntersection hd k (j ≫ f ≫ b) j A < 0) :
    ∃ a : X.functionFieldˣ, (A.rationalTwist a).Effective ∧
      ∀ η : X, Order.coheight η = 1 →
        (∀ U : Y.Opens, f η ∈ U → ¬ IsIso (f ∣_ U)) →
        0 < (A.rationalTwist a).coefficient hnX η := by
  classical
  obtain ⟨a, ha⟩ := exists_effective_cartier_rational_twist f hf A
  let E := A.rationalTwist a
  have hnonneg : ∀ x : X, 0 ≤ E.coefficient hnX x :=
    effective_cartierAtlas_weil_nonneg X hnX E ha
  refine ⟨a, ha, ?_⟩
  intro η hη hc
  by_contra hnot
  have hz : E.coefficient hnX η = 0 :=
    le_antisymm (le_of_not_gt hnot) (hnonneg η)
  let es : Unit → CartierAtlas X ι := fun _ => E
  let r : Unit → ℝ := fun _ => 1
  have he : ∀ x : X, 0 ≤ ∑ t, r t * ((es t).coefficient hnX x : ℝ) := by
    intro x
    simpa [r, es] using (show (0 : ℝ) ≤ (E.coefficient hnX x : ℝ) by
      exact_mod_cast hnonneg x)
  have hez : (∑ t, r t * ((es t).coefficient hnX η : ℝ)) = 0 := by
    simp [r, es, hz]
  obtain ⟨C, j, hC, hd, hp, hj, hconst, _, hI⟩ :=
    zero_exceptional_prime_actual_curve_nonnegative_intersection k b f hf hnX hnY
      η hη hc es r he hez
  have := hC
  have := hp
  have hI' : 0 ≤ normalizedCartierCurveIntersection hd k (j ≫ f ≫ b) j E := by
    have hreal : (0 : ℝ) ≤
        (normalizedCartierCurveIntersection hd k (j ≫ f ≫ b) j E : ℝ) := by
      simpa [normalizedRealCartierCurveIntersection, es, r] using hI
    exact_mod_cast hreal
  have hi := complete_integral_curve_ambient_cartier_principal_invariance
    hd k (j ≫ f ≫ b) j A a
  change normalizedCartierCurveIntersection hd k (j ≫ f ≫ b) j E = _ at hi
  rw [hi] at hI'
  exact (not_lt_of_ge hI') (hanti C hd j hj hconst)

end
end Negativity
