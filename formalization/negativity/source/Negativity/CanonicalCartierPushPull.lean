module

public import Negativity.CanonicalRealPullbackIntersection
public import Negativity.CartierPushPull
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the same canonical actual Cartier pullback used for
curve intersection and nefness satisfies actual proper birational
push-pull for every finite real Cartier sum. All local comparisons are
proved from actual codimension-one stalk isomorphisms. -/
theorem actual_canonical_real_cartier_push_pull
    {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (hnZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (p : Z ⟶ X) [IsProper p] (hp : BirationalMorphism p)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (d : τ → ℝ) :
    letI : IsDominant p := birationalMorphism_dominant p hp
    AlgebraicCycle.map p Order.coheight Order.coheight
      (∑ t, (actualCartierPullback p (A t)).weightedWeilCycle hnZ (d t)) =
        ∑ t, (A t).weightedWeilCycle hnX (d t) := by
  classical
  have : IsDominant p := birationalMorphism_dominant p hp
  let B t := actualCartierPullback p (A t)
  apply proper_birational_weil_cycle_pushforward hnX p hp _ _
  · simpa using cartierAtlas_real_sum_isWeilDivisor X hnX A d Finset.univ
  · simpa using cartierAtlas_real_sum_isWeilDivisor Z hnZ B d Finset.univ
  · intro z hz
    obtain ⟨w, hw, hst, hc, hu⟩ := proper_birational_codimensionOne_unique_preimage p hp (p z) hz
    have he : z = w := hu z rfl
    have hcz : Order.coheight z = 1 := he ▸ hc
    have : IsIso (p.stalkMap z) := he ▸ hst
    simp only [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    obtain ⟨i, hi⟩ := (B t).covers z
    obtain ⟨hle, _, heq⟩ := actualCartierPullback_data p (A t) i
    have hcoeff : (B t).coefficient hnZ z = (A t).coefficient hnX (p z) := by
      rw [cartierAtlas_coefficient_eq Z hnZ (B t) i z hcz hi,
        cartierAtlas_coefficient_eq X hnX (A t) ((A t).covers (p i)).choose (p z) hz (hle hi),
        heq]
      exact dominantFunctionFieldMap_order_of_stalk_iso hnZ hnX p z hcz hz _
    change d t * ((B t).coefficient hnZ z : ℝ) = d t * ((A t).coefficient hnX (p z) : ℝ)
    rw [hcoeff]

end
end Negativity
