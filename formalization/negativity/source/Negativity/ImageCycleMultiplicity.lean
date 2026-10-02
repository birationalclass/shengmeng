module

public import Negativity.CurveImageCases
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A closed immersion identifies actual residue fields at every point. -/
theorem closedImmersion_residueFieldMap_bijective {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] (y : Y) : Function.Bijective (j.residueFieldMap y) := by
  refine ⟨(j.residueFieldMap y).hom.injective, ?_⟩
  intro a
  obtain ⟨s, hs⟩ := Y.residue_surjective y a
  obtain ⟨t, ht⟩ := j.stalkMap_surjective y s
  refine ⟨X.residue (j y) t, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
  simpa only [CommRingCat.comp_apply, ht] using hs

/-- Passing through an actual closed immersion does not change the
residue-field multiplicity used by the actual cycle pushforward. -/
theorem residueDegree_comp_closedImmersion {C Y X : Scheme.{u}}
    (f : C ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion j] (x : C) :
    (f ≫ j).residueDegree x = f.residueDegree x := by
  let : Algebra (X.residueField (j (f x))) (C.residueField x) :=
    ((f ≫ j).residueFieldMap x).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (C.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let e := RingEquiv.ofBijective (j.residueFieldMap (f x)).hom
    (closedImmersion_residueFieldMap_bijective j (f x))
  change Module.finrank (X.residueField (j (f x))) (C.residueField x) =
    Module.finrank (Y.residueField (f x)) (C.residueField x)
  apply Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl (C.residueField x))
  change (j.residueFieldMap (f x) ≫ f.residueFieldMap x).hom =
    ((f ≫ j).residueFieldMap x).hom
  rw [Scheme.residueFieldMap_comp]

/-- Final theorem: the multiplicity of an actual curve cycle in an
ambient scheme is the full function-field degree to its actual image,
without supplying a field- or cycle-compatibility hypothesis. -/
theorem actual_image_residueDegree_functionField {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] :
    letI : IsIntegral f.image := proper_integral_actual_image_isIntegral f
    letI : Algebra f.image.functionField C.functionField :=
      (dominantFunctionFieldMap f.toImage).toAlgebra
    f.residueDegree (genericPoint C) = Module.finrank f.image.functionField C.functionField := by
  have : IsIntegral f.image := proper_integral_actual_image_isIntegral f
  let : Algebra f.image.functionField C.functionField :=
    (dominantFunctionFieldMap f.toImage).toAlgebra
  have h := residueDegree_comp_closedImmersion f.toImage f.imageι (genericPoint C)
  rw [Scheme.Hom.toImage_imageι] at h
  exact h.trans (dominant_generic_residueDegree_functionField f.toImage)

end
end Negativity
