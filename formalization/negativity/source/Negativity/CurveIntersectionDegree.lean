module

public import Negativity.CartierCurveIntersection
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem generic_stalk_functionField_self (C : Scheme) [IsIntegral C]
    (r : C.functionField) :
    @algebraMap (C.presheaf.stalk (genericPoint C)) C.functionField _ _
      (stalkFunctionFieldAlgebra C (genericPoint C)) r = r := by
  change (C.presheaf.stalkSpecializes (specializes_refl (genericPoint C))).hom r = r
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem genericPoint_not_cartier_support (X : Scheme) [IsIntegral X]
    {ι : Type*} (A : CartierAtlas X ι) : genericPoint X ∉ A.vanishingSupport := by
  let : Algebra (X.presheaf.stalk (genericPoint X)) X.functionField :=
    stalkFunctionFieldAlgebra X (genericPoint X)
  intro h
  apply h
  unfold RationalUnitAt
  have hF : IsField (X.presheaf.stalk (genericPoint X)) :=
    isField_stalk_of_closure_mem_irreducibleComponents X _
      (by simp [irreducibleComponents_eq_singleton])
  apply (Units.map_bijective (f := _) ?_).2
  exact ⟨IsFractionRing.injective _ _,
      (IsFractionRing.surjective_iff_isField
        (R := X.presheaf.stalk (genericPoint X)) (K := X.functionField)).mpr hF⟩

/-- An unmoved nondominant-style restriction agrees with the actual
generic-field pullback when the morphism is dominant. The compatibility
comes from the actual stalk square, not an intersection identity. -/
theorem dominant_moved_restriction_equations {C X : Scheme}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ X) [IsDominant f]
    {ι : Type*} (A : CartierAtlas X ι) (B : CartierAtlas C C)
    (hB : MovedCartierRestrictionData f A 1 B) (z : C) :
    B.equation z = Units.map (dominantFunctionFieldMap f).toMonoidHom
      (A.equation (A.covers (f z)).choose) := by
  obtain ⟨u, hu, hBu⟩ := (hB z).2.2
  rw [one_mul] at hu
  rw [hBu]
  apply Units.ext
  have hs := dominantFunctionFieldMap_stalk f (genericPoint C)
    (u : X.presheaf.stalk (f (genericPoint C)))
  rw [generic_stalk_functionField_self] at hs
  have hv := congrArg Units.val hu
  change algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField
    (u : X.presheaf.stalk (f (genericPoint C))) = _ at hv
  rw [hv] at hs
  exact hs.symm

/-- Final theorem: the choice-independent actual Cartier intersection for
a proper dominant map of complete normal curves equals the full function
field degree times the target Cartier degree. Actual finite pullback and
actual nondominant restriction are identified by their stalk equations.
The statement includes inseparable morphisms in arbitrary characteristic. -/
theorem complete_normal_curve_cartier_intersection_degree
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    [IsLocallyNoetherian C] [IsLocallyNoetherian X]
    (hnC : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdC : Order.krullDim C = 1) (hdX : Order.krullDim X = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (c : X ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) [IsProper f] [IsDominant f]
    {ι : Type*} (A : CartierAtlas X ι) :
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace c
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (f ≫ c)
    letI : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    cartierCurveIntersection hnC f A =
      (Module.finrank X.functionField C.functionField : ℤ) * cartierTotalOrder X hnX A := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace c
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (f ≫ c)
  let : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  have hη : f (genericPoint C) ∉ A.vanishingSupport := by
    rw [dominant_genericPoint_eq f]
    exact genericPoint_not_cartier_support X A
  obtain ⟨B, hB⟩ := exists_cartierAtlas_nondominant_pullback f A hη
  have hdata : MovedCartierRestrictionData f A 1 B := by
    intro z
    simpa only [one_mul] using hB z
  obtain ⟨P, hP, hdeg⟩ :=
    complete_normal_curve_cartier_pullback_degree f k c hnC hnX hdC hdX A
  have he : cartierOrderDivisor C hnC B = cartierOrderDivisor C hnC P := by
    ext x
    rw [cartierOrderDivisor_apply, cartierOrderDivisor_apply]
    by_cases hx : Order.coheight x = 1
    · rw [cartierAtlas_coefficient_eq C hnC B x x hx (hB x).1,
        cartierAtlas_coefficient_eq C hnC P x x hx (hP x).2.1,
        dominant_moved_restriction_equations f A B hdata x, (hP x).2.2]
    · simp [CartierAtlas.coefficient, hx]
  rw [complete_normal_curve_cartier_intersection_eq_restriction
    hnC hdC k (f ≫ c) f A 1 B hdata]
  unfold cartierTotalOrder
  rw [he]
  exact hdeg

end
end Negativity
