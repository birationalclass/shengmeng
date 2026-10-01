module

public import Negativity.CartierAtlas
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false

/-- A dominant morphism between integral schemes maps the actual generic
point to the actual generic point. -/
theorem dominant_genericPoint_eq {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  symm
  apply (genericPoint_spec Y).eq
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- Pullback on actual function fields, induced by the given Scheme morphism. -/
noncomputable def dominantFunctionFieldMap {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
    f.stalkMap (genericPoint X)).hom

/-- The generic pullback commutes with the actual local-ring pullback;
Cartier unit transition compatibility is proved from this square. -/
theorem dominantFunctionFieldMap_stalk {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (x : X) (r : Y.presheaf.stalk (f x)) :
    dominantFunctionFieldMap f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField r) =
      algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r) := by
  change ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
    (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
      f.stalkMap (genericPoint X)) r) =
        ((f.stalkMap x ≫ X.presheaf.stalkSpecializes
          ((genericPoint_spec X).specializes trivial)) r)
  simp only [TopCat.Presheaf.stalkCongr_inv, ← Category.assoc,
    TopCat.Presheaf.stalkSpecializes_comp]
  rw [Scheme.Hom.stalkSpecializes_stalkMap]

/-- Pullback of a Cartier atlas is constructed on affine neighborhoods in
the inverse images of its charts. No pullback divisor or unit compatibility
is taken as an additional input. -/
theorem exists_cartierAtlas_pullback {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] {ι : Type*} (A : CartierAtlas Y ι) :
    ∃ B : CartierAtlas X X, ∀ z : X,
      B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧ z ∈ B.chart z ∧
      B.equation z = Units.map (dominantFunctionFieldMap f : _ →* _)
        (A.equation (A.covers (f z)).choose) := by
  classical
  have ha (z : X) : ∃ V : X.Opens, IsAffineOpen V ∧ z ∈ V ∧
      V ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (A.covers (f z)).choose_spec (f ⁻¹ᵁ A.chart (A.covers (f z)).choose).isOpen
    exact ⟨V, hV, hzV, hVle⟩
  choose V hV hzV hle using ha
  let B : CartierAtlas X X := {
    chart := V
    affine := hV
    nonempty := fun z ↦ ⟨z, hzV z⟩
    covers := fun z ↦ ⟨z, hzV z⟩
    equation := fun z ↦ Units.map (dominantFunctionFieldMap f : _ →* _)
      (A.equation (A.covers (f z)).choose)
    transition := by
      intro z w x hz hw
      obtain ⟨u, hu⟩ := A.transition _ _ (f x) (hle z hz) (hle w hw)
      refine ⟨Units.map ((f.stalkMap x).hom : _ →* _) u, ?_⟩
      apply Units.ext
      have hc := congrArg (fun v : Y.functionFieldˣ ↦
        dominantFunctionFieldMap f (v : Y.functionField)) hu
      simp only [Units.val_mul, Units.coe_map, map_mul] at hc
      change dominantFunctionFieldMap f
        (algebraMap (Y.presheaf.stalk (f x)) Y.functionField (u : Y.presheaf.stalk (f x))) *
        dominantFunctionFieldMap f (A.equation (A.covers (f z)).choose : Y.functionField) =
        dominantFunctionFieldMap f (A.equation (A.covers (f w)).choose : Y.functionField) at hc
      rw [dominantFunctionFieldMap_stalk f x (u : Y.presheaf.stalk (f x))] at hc
      exact hc }
  exact ⟨B, fun z ↦ ⟨hle z, hzV z, rfl⟩⟩

/-- At an actual local-ring isomorphism the pulled-back rational equation
has the same codimension-one order. Compatibility with the generic map
is proved above, rather than supplied as an intersection-theory input. -/
theorem dominantFunctionFieldMap_order_of_stalk_iso {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (f : X ⟶ Y) [IsDominant f] (x : X) [IsIso (f.stalkMap x)]
    (hx : Order.coheight x = 1) (hy : Order.coheight (f x) = 1)
    (a : Y.functionFieldˣ) :
    schemeRationalOrder X hnX x hx (Units.map (dominantFunctionFieldMap f : _ →* _) a) =
      schemeRationalOrder Y hnY (f x) hy a := by
  have := hnX x
  have := hnY (f x)
  have := normal_codimensionOne_stalk_isDVR X x hx
  have := normal_codimensionOne_stalk_isDVR Y (f x) hy
  let R := Y.presheaf.stalk (f x)
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) (a : Y.functionField)
  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hr : r ≠ 0 := by
    intro hz
    have hsk : algebraMap R Y.functionField (s : R) ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R Y.functionField).ne hs
    exact mul_ne_zero a.ne_zero hsk (by simpa only [hz, map_zero] using h)
  have hs' : (f.stalkMap x).hom (s : R) ≠ 0 := by
    simpa only [map_zero] using (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).1.ne hs
  have hr' : (f.stalkMap x).hom r ≠ 0 := by
    simpa only [map_zero] using (ConcreteCategory.bijective_of_isIso (f.stalkMap x)).1.ne hr
  unfold schemeRationalOrder
  rw [dvr_rationalOrder_represents _ _ a r s hr hs h]
  rw [dvr_rationalOrder_represents _ _ _ _ _ hr' hs' (by
    have hc := congrArg (dominantFunctionFieldMap f) h
    rw [map_mul, dominantFunctionFieldMap_stalk f x (s : R),
      dominantFunctionFieldMap_stalk f x r] at hc
    exact hc)]
  exact scheme_stalk_fraction_order_of_iso f x r s

end Negativity
