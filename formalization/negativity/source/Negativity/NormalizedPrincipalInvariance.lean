module

public import Negativity.NormalizedCurveIntersection
public import Negativity.AmbientCartierMoving
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Final theorem: actual Cartier intersection on any complete integral
curve is invariant under a principal twist of the ambient divisor.
Normalization is constructed and proved finite; no normality of the
original curve and no restriction of the principal function to it is
assumed. -/
theorem complete_integral_curve_ambient_cartier_principal_invariance
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) (a : X.functionFieldˣ) :
    normalizedCartierCurveIntersection hd k c f (A.rationalTwist a) =
      normalizedCartierCurveIntersection hd k c f A := by
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  exact complete_normal_curve_ambient_cartier_principal_invariance
    (generic_normalization_stalks_normal C) h.2.2.2.2.1 k
    (n.fromNormalization ≫ c) (n.fromNormalization ≫ f) A a

end
end Negativity
