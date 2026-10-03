module

public import Negativity.CanonicalRealPullbackIntersection
public import Negativity.FiniteNormalGeometry
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Actual open restriction preserves every actual Cartier coefficient.
The restricted atlas is the genuine fixed Cartier pullback, and its
stalk equations and local DVR orders are proved compatible. -/
theorem actual_cartier_open_restriction_coefficient
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] {ι : Type*} (A : CartierAtlas X ι) :
    letI : IsDominant U.ι := Opens.isDominant_ι
      (U.isOpen.dense (by simpa using ‹Nonempty U›))
    ∀ x : U.toScheme,
      (actualCartierPullback U.ι A).coefficient (normalStalks_restrict X U hnX) x =
        A.coefficient hnX (U.ι x) := by
  let : IsDominant U.ι := Opens.isDominant_ι
    (U.isOpen.dense (by simpa using ‹Nonempty U›))
  intro x
  have hheight : Order.coheight (U.ι x) = Order.coheight x :=
    coheight_eq_of_isOpenImmersion U.ι
  by_cases hx : Order.coheight x = 1
  · have hy : Order.coheight (U.ι x) = 1 := hheight.trans hx
    have hd := actualCartierPullback_data U.ι A x
    rw [cartierAtlas_coefficient_eq U.toScheme (normalStalks_restrict X U hnX)
      (actualCartierPullback U.ι A) x x hx hd.2.1,
      cartierAtlas_coefficient_eq X hnX A (A.covers (U.ι x)).choose (U.ι x)
        hy (A.covers (U.ι x)).choose_spec, hd.2.2]
    exact dominantFunctionFieldMap_order_of_stalk_iso
      (normalStalks_restrict X U hnX) hnX U.ι x hx hy _
  · have hy : Order.coheight (U.ι x) ≠ 1 := by rwa [hheight]
    change Order.coheight x.1 ≠ 1 at hy
    simp [CartierAtlas.coefficient, hx, hy]

/-- Final theorem: the finite real Weil cycle of the fixed actual open
Cartier restriction has exactly the original real coefficients on that
actual open. No coefficient-comparison input is supplied. -/
theorem actual_real_cartier_open_restriction_cycle
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) [Nonempty U] {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : IsDominant U.ι := Opens.isDominant_ι
      (U.isOpen.dense (by simpa using ‹Nonempty U›))
    ∀ x : U.toScheme,
      (∑ t, (actualCartierPullback U.ι (A t)).weightedWeilCycle
        (normalStalks_restrict X U hnX) (r t)) x =
      (∑ t, (A t).weightedWeilCycle hnX (r t)) (U.ι x) := by
  let : IsDominant U.ι := Opens.isDominant_ι
    (U.isOpen.dense (by simpa using ‹Nonempty U›))
  intro x
  simp [CartierAtlas.weightedWeilCycle, CartierAtlas.weilCycle,
    actual_cartier_open_restriction_coefficient hnX U]

end
end Negativity
