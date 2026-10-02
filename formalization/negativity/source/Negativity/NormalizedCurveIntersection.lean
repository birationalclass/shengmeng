module

public import Negativity.CurveNormalization
public import Negativity.RealIntersectionPresentations
public import Negativity.RealIntersectionPullback
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
noncomputable section

/-- Cartier intersection for any actual complete integral curve, including
singular and nonnormal curves, is the local-order intersection on its
constructed finite normalization. -/
def normalizedCartierCurveIntersection
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) : ℤ := by
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  exact cartierCurveIntersection (generic_normalization_stalks_normal C)
    (n.fromNormalization ≫ f) A

/-- The actual real intersection on an arbitrary complete integral curve. -/
def normalizedRealCartierCurveIntersection
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (r : τ → ℝ) : ℝ :=
  ∑ t, r t * (normalizedCartierCurveIntersection hd k c f (A t) : ℝ)

theorem complete_integral_curve_real_intersection_point_image_zero
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) (hpoint : ∀ x : C, f x = f (genericPoint C))
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    normalizedRealCartierCurveIntersection hd k c f A r = 0 := by
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  have hp : ∀ x : n.normalization, (n.fromNormalization ≫ f) x =
      (n.fromNormalization ≫ f) (genericPoint n.normalization) := by
    intro x
    exact (hpoint (n.fromNormalization x)).trans
      (hpoint (n.fromNormalization (genericPoint n.normalization))).symm
  exact complete_normal_curve_real_cartier_intersection_point_image_zero
    (generic_normalization_stalks_normal C) h.2.2.2.2.1 k
    (n.fromNormalization ≫ c) (n.fromNormalization ≫ f) hp A r

/-- Final theorem: arbitrary actual real Cartier presentations define the
same intersection on every complete integral curve. The curve need not
be normal or smooth: finite normality and dimension of its actual
normalization are proved before applying local-order invariance. -/
theorem complete_integral_curve_real_cartier_presentation_independent
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian X]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι κ τ σ : Type*} [Fintype τ] [Fintype σ]
    (A : τ → CartierAtlas X ι) (B : σ → CartierAtlas X κ)
    (r : τ → ℝ) (s : σ → ℝ)
    (heq : ∀ x : X, (∑ t, r t * ((A t).coefficient hnX x : ℝ)) =
      ∑ j, s j * ((B j).coefficient hnX x : ℝ)) :
    normalizedRealCartierCurveIntersection hd k c f A r =
      normalizedRealCartierCurveIntersection hd k c f B s := by
  let n := C.fromSpecStalk (genericPoint C)
  have h := complete_integral_curve_normalization_properties C hd k c
  have : IsLocallyNoetherian n.normalization := h.2.2.2.2.2.1
  have : IsProper (n.fromNormalization ≫ c) := h.2.2.2.2.2.2
  let : CompactSpace n.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (n.fromNormalization ≫ c)
  exact complete_normal_curve_real_cartier_presentation_independent
    (generic_normalization_stalks_normal C) hnX h.2.2.2.2.1 k
    (n.fromNormalization ≫ c) (n.fromNormalization ≫ f) A B r s heq

end
end Negativity
