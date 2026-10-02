module

public import Negativity.CurveRestrictionComposition
public import Negativity.CurveNormalizationLift
public import Negativity.NormalizedCurveIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: actual Cartier intersection on arbitrary complete
integral curves satisfies the projection formula for a proper dominant
curve map and any ambient curve map. Neither original curve is normal
or smooth; both normalizations and the commuting lift are constructed.
The multiplicity is the full original function-field degree. -/
theorem complete_integral_curve_cartier_projection
    {C Y X : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsIntegral X]
    (hdC : Order.krullDim C = 1) (hdY : Order.krullDim Y = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [IsProper b]
    (f : C ⟶ Y) [IsProper f] [IsDominant f] (j : Y ⟶ X)
    {ι : Type*} (A : CartierAtlas X ι) :
    letI : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    normalizedCartierCurveIntersection hdC k (f ≫ b) (f ≫ j) A =
      (Module.finrank Y.functionField C.functionField : ℤ) *
        normalizedCartierCurveIntersection hdY k b j A := by
  let nC := C.fromSpecStalk (genericPoint C)
  let nY := Y.fromSpecStalk (genericPoint Y)
  let : Algebra Y.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  have hC := complete_integral_curve_normalization_properties C hdC k (f ≫ b)
  have hY := complete_integral_curve_normalization_properties Y hdY k b
  have : IsLocallyNoetherian nC.normalization := hC.2.2.2.2.2.1
  have : IsLocallyNoetherian nY.normalization := hY.2.2.2.2.2.1
  have : IsProper (nY.fromNormalization ≫ b) := hY.2.2.2.2.2.2
  obtain ⟨l, hl, hlf, hld, hdegree⟩ :=
    complete_integral_curves_normalization_lift_degree hdC hdY k b f
  have : IsFinite l := hlf
  have : IsDominant l := hld
  let : Algebra nY.normalization.functionField nC.normalization.functionField :=
    (dominantFunctionFieldMap l).toAlgebra
  have hI := complete_normal_curve_cartier_intersection_reparametrization
    (generic_normalization_stalks_normal C) (generic_normalization_stalks_normal Y)
    hC.2.2.2.2.1 hY.2.2.2.2.1 k (nY.fromNormalization ≫ b) l
    (nY.fromNormalization ≫ j) A
  rw [hdegree] at hI
  have hcomp : l ≫ (nY.fromNormalization ≫ j) = nC.fromNormalization ≫ (f ≫ j) := by
    rw [← Category.assoc, hl, Category.assoc]
  rw [hcomp] at hI
  simpa only [normalizedCartierCurveIntersection] using hI

end
end Negativity
