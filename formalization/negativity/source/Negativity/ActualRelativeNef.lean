module

public import Negativity.CanonicalRealPullbackIntersection
public import Negativity.ActualProjectionFormula
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Relative nefness tested on actual complete integral curves contracted
by the actual map. Intersection is the constructed normalization/local-
order intersection, not a supplied numerical linear map. -/
def ActualRelativeNef {X S : Scheme.{u}} [IsIntegral X]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) (f : X ⟶ S)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) : Prop :=
  ∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
    (g : C ⟶ X) [IsProper (g ≫ b)],
    (∀ x : C, (g ≫ f) x = (g ≫ f) (genericPoint C)) →
      0 ≤ normalizedRealCartierCurveIntersection hd k (g ≫ b) g A r

/-- The minus-divisor sign in negativity is exactly actual relative
nefness, on actual contracted complete curves only. -/
theorem actual_relative_nef_negative_iff {X S : Scheme.{u}} [IsIntegral X]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) (f : X ⟶ S)
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ) :
    ActualRelativeNef k b f A (fun t => -r t) ↔
      ∀ (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
        (g : C ⟶ X) [IsProper (g ≫ b)],
        (∀ x : C, (g ≫ f) x = (g ≫ f) (genericPoint C)) →
          normalizedRealCartierCurveIntersection hd k (g ≫ b) g A r ≤ 0 := by
  simp [ActualRelativeNef, normalizedRealCartierCurveIntersection, Finset.sum_neg_distrib]

/-- Final theorem: genuine relative nefness is preserved by the same
fixed actual dominant Cartier pullback for all contracted complete
curves. Actual image completeness, contraction and degree scaling are
proved, and no geometric projection/nef-transport input is assumed. -/
theorem actual_relative_nef_canonical_pullback {Y X S : Scheme.{u}}
    [IsIntegral Y] [IsIntegral X]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    (f : X ⟶ S) (p : Y ⟶ X) [IsDominant p]
    {ι τ : Type*} [Fintype τ] (A : τ → CartierAtlas X ι) (r : τ → ℝ)
    (hnef : ActualRelativeNef k b f A r) :
    ActualRelativeNef k (p ≫ b) (p ≫ f) (fun t => actualCartierPullback p (A t)) r := by
  classical
  intro C _ hd g _ hcontract
  have : IsProper ((g ≫ p) ≫ b) := by rw [Category.assoc]; infer_instance
  have : IsProper (g ≫ p) := IsProper.of_comp (g ≫ p) b
  have hprops := complete_integral_curve_actual_image_properties hd k b (g ≫ p)
  have : IsProper (g ≫ p).toImage := hprops.1
  have : IsIntegral (g ≫ p).image := hprops.2.2.1
  have : IsProper ((g ≫ p).imageι ≫ b) := hprops.2.2.2.1
  have hI := complete_integral_curve_canonical_real_pullback_intersection hd k
    (g ≫ (p ≫ b)) p g A r
  rw [hI]
  rcases complete_integral_curve_actual_image_dichotomy hd k b (g ≫ p) A r with ⟨_, hz⟩ | hi
  · have hz' : normalizedRealCartierCurveIntersection hd k (g ≫ (p ≫ b)) (g ≫ p) A r = 0 := by
      simpa only [Category.assoc] using hz
    rw [hz']
  · have hconst : ∀ y : (g ≫ p).image,
        ((g ≫ p).imageι ≫ f) y = ((g ≫ p).imageι ≫ f) (genericPoint (g ≫ p).image) := by
      intro y
      obtain ⟨x, rfl⟩ := (g ≫ p).toImage.surjective y
      have hx := hcontract x
      have he := dominant_genericPoint_eq (g ≫ p).toImage
      rw [← he]
      simpa only [← Scheme.Hom.comp_apply, Category.assoc,
        Scheme.Hom.toImage_imageι_assoc] using hx
    have hnonneg := hnef (g ≫ p).image hi (g ≫ p).imageι hconst
    let : Algebra (g ≫ p).image.functionField C.functionField :=
      (dominantFunctionFieldMap (g ≫ p).toImage).toAlgebra
    have hp := complete_integral_curve_real_cartier_projection hd hi k
      ((g ≫ p).imageι ≫ b) (g ≫ p).toImage (g ≫ p).imageι A r
    have hscaled := mul_nonneg
      (Nat.cast_nonneg (Module.finrank (g ≫ p).image.functionField C.functionField) :
        (0 : ℝ) ≤ _) hnonneg
    have hdegree : normalizedRealCartierCurveIntersection hd k ((g ≫ p) ≫ b) (g ≫ p) A r =
        (Module.finrank (g ≫ p).image.functionField C.functionField : ℝ) *
          normalizedRealCartierCurveIntersection hi k ((g ≫ p).imageι ≫ b)
            (g ≫ p).imageι A r := by
      simpa only [← Category.assoc, Scheme.Hom.toImage_imageι] using hp
    have hn : 0 ≤ normalizedRealCartierCurveIntersection hd k ((g ≫ p) ≫ b) (g ≫ p) A r := by
      rw [hdegree]
      exact hscaled
    simpa only [Category.assoc] using hn

end
end Negativity
