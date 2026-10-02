module

public import Negativity.CartierDegree
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem stalkSpecialization_functionField (Y : Scheme) [IsIntegral Y]
    (y z : Y) (h : y ⤳ z) (r : Y.presheaf.stalk z) :
    algebraMap (Y.presheaf.stalk y) Y.functionField ((Y.presheaf.stalkSpecializes h).hom r) =
      algebraMap (Y.presheaf.stalk z) Y.functionField r := by
  change ((Y.presheaf.stalkSpecializes h ≫ Y.presheaf.stalkSpecializes
    ((genericPoint_spec Y).specializes trivial)) r) = _
  simp only [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

theorem generic_stalkMap_commutes {X Y : Scheme} [IsIntegral X]
    (f : X ⟶ Y) (x : X) (r : Y.presheaf.stalk (f x)) :
    (f.stalkMap (genericPoint X)).hom
      ((Y.presheaf.stalkSpecializes
        (f.base.hom.map_specializes ((genericPoint_spec X).specializes trivial))).hom r) =
      algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r) := by
  exact f.stalkSpecializes_stalkMap_apply (genericPoint X) x
    ((genericPoint_spec X).specializes trivial) r

/-- Genuine Cartier restriction to an integral curve (or integral scheme)
whose generic image avoids the divisor support. No dominance of f, curve
intersection map, or Cartier-compatibility identity is assumed. -/
theorem exists_cartierAtlas_nondominant_pullback {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    {ι : Type*} (A : CartierAtlas Y ι)
    (hη : f (genericPoint X) ∉ A.vanishingSupport) :
    ∃ B : CartierAtlas X X, ∀ z : X,
      z ∈ B.chart z ∧ B.chart z ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose ∧
      ∃ u : (Y.presheaf.stalk (f (genericPoint X)))ˣ,
        Units.map (algebraMap (Y.presheaf.stalk (f (genericPoint X))) Y.functionField).toMonoidHom u =
          A.equation (A.covers (f z)).choose ∧
        B.equation z = Units.map (f.stalkMap (genericPoint X)).hom.toMonoidHom u := by
  have hi (z : X) : f (genericPoint X) ∈ A.chart (A.covers (f z)).choose :=
    (f.base.hom.map_specializes ((genericPoint_spec X).specializes trivial)).mem_open
      (A.chart (A.covers (f z)).choose).isOpen (A.covers (f z)).choose_spec
  have hu (z : X) : RationalUnitAt Y (f (genericPoint X))
      (A.equation (A.covers (f z)).choose) := by
    by_contra hz
    exact hη ((cartierAtlas_support_eq_on_chart Y A _ _ (hi z)).mpr hz)
  choose u hu using hu
  have ha (z : X) : ∃ V : X.Opens, IsAffineOpen V ∧ z ∈ V ∧
      V ≤ f ⁻¹ᵁ A.chart (A.covers (f z)).choose := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (A.covers (f z)).choose_spec (f ⁻¹ᵁ A.chart (A.covers (f z)).choose).isOpen
    exact ⟨V, hV, hzV, hle⟩
  choose V hV hzV hle using ha
  let B : CartierAtlas X X := {
    chart := V
    affine := hV
    nonempty := fun z => ⟨z, hzV z⟩
    covers := fun z => ⟨z, hzV z⟩
    equation := fun z => Units.map (f.stalkMap (genericPoint X)).hom.toMonoidHom (u z)
    transition := by
      intro z w x hz hw
      obtain ⟨v, hv⟩ := A.transition _ _ (f x) (hle z hz) (hle w hw)
      let sp : Y.presheaf.stalk (f x) →+* Y.presheaf.stalk (f (genericPoint X)) :=
        (Y.presheaf.stalkSpecializes
        (f.base.hom.map_specializes ((genericPoint_spec X).specializes trivial))).hom
      have hs : Units.map (algebraMap (Y.presheaf.stalk (f (genericPoint X))) Y.functionField).toMonoidHom
          (Units.map sp.toMonoidHom v) =
          Units.map (algebraMap (Y.presheaf.stalk (f x)) Y.functionField).toMonoidHom v := by
        apply Units.ext
        exact stalkSpecialization_functionField Y _ _ _ (v : Y.presheaf.stalk (f x))
      have he : Units.map sp.toMonoidHom v * u z = u w := by
        apply Units.ext
        apply IsFractionRing.injective (Y.presheaf.stalk (f (genericPoint X))) Y.functionField
        change (Units.map (algebraMap (Y.presheaf.stalk (f (genericPoint X))) Y.functionField).toMonoidHom
          (Units.map sp.toMonoidHom v * u z) : Y.functionField) =
          (Units.map (algebraMap (Y.presheaf.stalk (f (genericPoint X))) Y.functionField).toMonoidHom (u w) : Y.functionField)
        exact congrArg Units.val (calc
          _ = _ := map_mul _ _ _
          _ = _ := congrArg₂ (fun a b => a * b) hs (hu z)
          _ = _ := hv
          _ = _ := (hu w).symm)
      refine ⟨Units.map (f.stalkMap x).hom.toMonoidHom v, ?_⟩
      have hsX : Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom
          (Units.map (f.stalkMap x).hom.toMonoidHom v) =
          Units.map (f.stalkMap (genericPoint X)).hom.toMonoidHom
            (Units.map sp.toMonoidHom v) := by
        apply Units.ext
        exact (generic_stalkMap_commutes f x (v : Y.presheaf.stalk (f x))).symm
      exact calc
        _ = _ := congrArg (fun a => a * Units.map
          (f.stalkMap (genericPoint X)).hom.toMonoidHom (u z)) hsX
        _ = _ := (map_mul _ _ _).symm
        _ = _ := congrArg (fun t : (Y.presheaf.stalk (f (genericPoint X)))ˣ =>
          Units.map (f.stalkMap (genericPoint X)).hom.toMonoidHom t) he }
  exact ⟨B, fun z => ⟨hzV z, hle z, u z, hu z, rfl⟩⟩

/-- Effective Cartier restriction along an arbitrary Scheme morphism whose
integral source is not contained in the support. Its regular equations and
full inverse-image support are constructed from actual stalk maps. -/
theorem exists_effective_nondominant_cartier_pullback {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    {ι : Type*} (A : CartierAtlas Y ι) (hA : A.Effective)
    (hη : f (genericPoint X) ∉ A.vanishingSupport) :
    ∃ B : CartierAtlas X X, B.Effective ∧
      B.vanishingSupport = f ⁻¹' A.vanishingSupport ∧
      ∀ z (x : X), x ∈ B.chart z →
        ∃ r : Y.presheaf.stalk (f x),
          algebraMap (Y.presheaf.stalk (f x)) Y.functionField r =
            (A.equation (A.covers (f z)).choose : Y.functionField) ∧
          algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r) =
            (B.equation z : X.functionField) := by
  obtain ⟨B, hB⟩ := exists_cartierAtlas_nondominant_pullback f A hη
  have hregular (z x : X) (hx : x ∈ B.chart z) :
      ∃ r : Y.presheaf.stalk (f x),
        algebraMap (Y.presheaf.stalk (f x)) Y.functionField r =
          (A.equation (A.covers (f z)).choose : Y.functionField) ∧
        algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom r) =
          (B.equation z : X.functionField) := by
    obtain ⟨r, hr⟩ := hA _ (f x) ((hB z).2.1 hx)
    obtain ⟨u, hu, hBu⟩ := (hB z).2.2
    let sp : Y.presheaf.stalk (f x) →+* Y.presheaf.stalk (f (genericPoint X)) :=
      (Y.presheaf.stalkSpecializes
        (f.base.hom.map_specializes ((genericPoint_spec X).specializes trivial))).hom
    have he : sp r = (u : Y.presheaf.stalk (f (genericPoint X))) := by
      apply IsFractionRing.injective (Y.presheaf.stalk (f (genericPoint X))) Y.functionField
      exact (stalkSpecialization_functionField Y _ _ _ r).trans
        (hr.trans (congrArg Units.val hu).symm)
    refine ⟨r, hr, ?_⟩
    exact calc
      _ = (f.stalkMap (genericPoint X)).hom (sp r) :=
        (generic_stalkMap_commutes f x r).symm
      _ = (f.stalkMap (genericPoint X)).hom (u : Y.presheaf.stalk (f (genericPoint X))) :=
        congrArg (f.stalkMap (genericPoint X)).hom he
      _ = _ := (congrArg Units.val hBu).symm
  have hBe : B.Effective := by
    intro z x hx
    obtain ⟨r, _, hr⟩ := hregular z x hx
    exact ⟨(f.stalkMap x).hom r, hr⟩
  refine ⟨B, hBe, ?_, hregular⟩
  ext x
  rw [cartierAtlas_support_eq_on_chart X B x x (hB x).1, Set.mem_preimage,
    cartierAtlas_support_eq_on_chart Y A _ (f x) (A.covers (f x)).choose_spec]
  obtain ⟨r, hr, hs⟩ := hregular x x (hB x).1
  rw [rationalUnitAt_regular_iff X x _ _ hs,
    rationalUnitAt_regular_iff Y (f x) _ r hr]
  exact not_congr (isUnit_map_iff (f.stalkMap x).hom r)

/-- The effective-divisor intersection sign on a proper normal integral
curve, defined directly as the sum of orders of its Cartier restriction.
No ambient dominance or assumed intersection positivity is used. -/
theorem effective_cartier_restriction_order_signs {C X : Scheme}
    [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C] [CompactSpace C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective)
    (hη : f (genericPoint C) ∉ A.vanishingSupport) :
    ∃ B : CartierAtlas C C, B.Effective ∧
      B.vanishingSupport = f ⁻¹' A.vanishingSupport ∧
      0 ≤ cartierTotalOrder C hn B ∧
      ((f ⁻¹' A.vanishingSupport).Nonempty → 0 < cartierTotalOrder C hn B) := by
  obtain ⟨B, hB, hS, _⟩ := exists_effective_nondominant_cartier_pullback f A hA hη
  refine ⟨B, hB, hS, effective_cartierTotalOrder_nonneg C hn B hB, ?_⟩
  intro hmeet
  apply effective_cartierTotalOrder_pos_of_support C hn B hB
  exact hS.symm ▸ hmeet

end Negativity
