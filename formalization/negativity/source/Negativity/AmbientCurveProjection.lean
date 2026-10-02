module

public import Negativity.ImageCycleMultiplicity
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Function.locallyFinsuppWithin
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Intersection on the actual scheme-theoretic image curve, with zero
for a point image. All image properties are derived from the actual map. -/
def actualImageRealCartierIntersection
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hdC : Order.krullDim C = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (f : C ⟶ X) [IsProper (f ≫ b)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) : ℝ := by
  classical
  have h := complete_integral_curve_actual_image_properties hdC k b f
  have : IsIntegral f.image := h.2.2.1
  have : IsProper (f.imageι ≫ b) := h.2.2.2.1
  exact if hd : Order.krullDim f.image = 1 then
    normalizedRealCartierCurveIntersection hd k (f.imageι ≫ b) f.imageι A r else 0

/-- Final theorem: actual ambient projection formula for arbitrary real
Cartier combinations on any complete integral curve. The image, dimension
alternatives, normalization, full field degree and actual cycle
multiplicity are constructed or proved. No intersection identity,
separability, normality of the original curves, or image-curve input is
assumed. -/
theorem complete_integral_curve_ambient_real_projection
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hdC : Order.krullDim C = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (f : C ⟶ X) [IsProper (f ≫ b)]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    letI : IsProper f := IsProper.of_comp f b
    letI : DecidableEq C := Classical.decEq C
    letI : DecidableEq X := Classical.decEq X
    normalizedRealCartierCurveIntersection hdC k (f ≫ b) f A r =
      (AlgebraicCycle.map f Order.height Order.height (single (genericPoint C) (1 : ℝ)))
        (f (genericPoint C)) * actualImageRealCartierIntersection hdC k b f A r := by
  classical
  have : IsProper f := IsProper.of_comp f b
  have h := complete_integral_curve_actual_image_properties hdC k b f
  have : IsProper f.toImage := h.1
  have : IsIntegral f.image := h.2.2.1
  have : IsProper (f.imageι ≫ b) := h.2.2.2.1
  let : Algebra f.image.functionField C.functionField :=
    (dominantFunctionFieldMap f.toImage).toAlgebra
  rcases complete_integral_curve_actual_image_dichotomy hdC k b f A r with ⟨hs, hz⟩ | hd
  · have hd0 : Order.krullDim f.image = 0 := @Order.krullDim_eq_zero _ _ inferInstance hs
    rw [hz]
    simp only [actualImageRealCartierIntersection, hd0, zero_ne_one, dite_false, mul_zero]
  · have hwt : Order.height (genericPoint C) = Order.height (f (genericPoint C)) := by
      have he := (curve_generic_height_preserved hdC hd f.toImage).trans
        (closedImmersion_height_eq f.imageι (f.toImage (genericPoint C)))
      simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using he
    rw [scheme_cycle_map_single,
      scheme_mapCoeff_of_same_weight f Order.height Order.height (genericPoint C) hwt,
      one_mul]
    simp only [single_apply, ite_true]
    rw [actual_image_residueDegree_functionField f]
    have hv : actualImageRealCartierIntersection hdC k b f A r =
        normalizedRealCartierCurveIntersection hd k (f.imageι ≫ b) f.imageι A r := by
      simp only [actualImageRealCartierIntersection, dite_eq_left hd]
    rw [hv]
    have hp := complete_integral_curve_real_cartier_projection hdC hd k
      (f.imageι ≫ b) f.toImage f.imageι A r
    simpa only [← Category.assoc, Scheme.Hom.toImage_imageι] using hp

end
end Negativity
