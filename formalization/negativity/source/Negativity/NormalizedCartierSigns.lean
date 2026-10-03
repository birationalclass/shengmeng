module

public import Negativity.NormalizedCurveIntersection
public import Negativity.EffectiveCurveIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Final theorem: an actual effective Cartier divisor has nonnegative
intersection on every complete integral curve outside its support, and
strictly positive intersection if they meet. The actual finite normalization
also handles singular and nonnormal curves. -/
theorem complete_integral_curve_effective_cartier_intersection_signs
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective)
    (hη : f (genericPoint C) ∉ A.vanishingSupport) :
    0 ≤ normalizedCartierCurveIntersection hd k c f A ∧
      ((f ⁻¹' A.vanishingSupport).Nonempty →
        0 < normalizedCartierCurveIntersection hd k c f A) := by
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  have : IsDominant n.fromNormalization := birationalMorphism_dominant n.fromNormalization h.2.1
  have hηN : (n.fromNormalization ≫ f) (genericPoint n.normalization) ∉ A.vanishingSupport := by
    simpa only [Scheme.Hom.comp_apply, dominant_genericPoint_eq n.fromNormalization] using hη
  have hp := complete_normal_curve_effective_cartier_intersection_signs
    (generic_normalization_stalks_normal C) h.2.2.2.2.1 k
    (n.fromNormalization ≫ c) (n.fromNormalization ≫ f) A hA hηN
  refine ⟨hp.1, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨z, hz⟩ := h.2.2.1.surj x
  change n.fromNormalization z = x at hz
  apply hp.2
  refine ⟨z, ?_⟩
  change f (n.fromNormalization z) ∈ A.vanishingSupport
  rw [hz]
  exact hx

end
end Negativity
