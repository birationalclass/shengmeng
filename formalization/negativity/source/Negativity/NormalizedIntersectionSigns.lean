module

public import Negativity.NormalizedCurveIntersection
public import Negativity.EffectiveRealIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: effective actual real Cartier divisors have
nonnegative intersection on arbitrary complete integral curves outside
their support, and positive intersection when they meet the curve.
The actual finite normalization transfers both the generic avoidance
and the support meeting; the original curve may be nonnormal. -/
theorem complete_integral_curve_effective_real_intersection_signs
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (he : ∀ x : X, 0 ≤ ∑ t, r t * ((A t).coefficient hnX x : ℝ))
    (hη : f (genericPoint C) ∉ closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support) :
    0 ≤ normalizedRealCartierCurveIntersection hd k c f A r ∧
      ((f ⁻¹' closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support).Nonempty →
        0 < normalizedRealCartierCurveIntersection hd k c f A r) := by
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  have : IsDominant n.fromNormalization := birationalMorphism_dominant n.fromNormalization h.2.1
  have hηN : (n.fromNormalization ≫ f) (genericPoint n.normalization) ∉
      closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support := by
    simpa only [Scheme.Hom.comp_apply, dominant_genericPoint_eq n.fromNormalization] using hη
  have hp := complete_normal_curve_effective_real_cartier_intersection_signs
    (generic_normalization_stalks_normal C) hnX h.2.2.2.2.1 k
    (n.fromNormalization ≫ c) (n.fromNormalization ≫ f) A r he hηN
  refine ⟨hp.1, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨z, hz⟩ := h.2.2.1.surj x
  change n.fromNormalization z = x at hz
  apply hp.2
  refine ⟨z, ?_⟩
  change f (n.fromNormalization z) ∈
    closure (∑ t, (A t).weightedWeilCycle hnX (r t)).support
  rw [hz]
  exact hx

end
end Negativity
