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

/-- Retain the actual stalk pullback data while proving effectivity and
full support pullback. These are outputs of actual local regular equations,
not intersection-sign or support-equality hypotheses. -/
theorem effective_cartier_restriction_with_data {C X : Scheme}
    [IsIntegral C] [IsIntegral X] (f : C ⟶ X)
    {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective)
    (hη : f (genericPoint C) ∉ A.vanishingSupport) :
    ∃ B : CartierAtlas C C, MovedCartierRestrictionData f A 1 B ∧
      B.Effective ∧ B.vanishingSupport = f ⁻¹' A.vanishingSupport := by
  classical
  obtain ⟨B, hB⟩ := exists_cartierAtlas_nondominant_pullback f A hη
  have hregular (z x : C) (hx : x ∈ B.chart z) :
      ∃ r : X.presheaf.stalk (f x),
        algebraMap (X.presheaf.stalk (f x)) X.functionField r =
          (A.equation (A.covers (f z)).choose : X.functionField) ∧
        algebraMap (C.presheaf.stalk x) C.functionField ((f.stalkMap x).hom r) =
          (B.equation z : C.functionField) := by
    obtain ⟨r, hr⟩ := hA _ (f x) ((hB z).2.1 hx)
    obtain ⟨u, hu, hBu⟩ := (hB z).2.2
    let sp : X.presheaf.stalk (f x) →+* X.presheaf.stalk (f (genericPoint C)) :=
      (X.presheaf.stalkSpecializes
        (f.base.hom.map_specializes ((genericPoint_spec C).specializes trivial))).hom
    have he : sp r = (u : X.presheaf.stalk (f (genericPoint C))) := by
      apply IsFractionRing.injective (X.presheaf.stalk (f (genericPoint C))) X.functionField
      exact (stalkSpecialization_functionField X _ _ _ r).trans
        (hr.trans (congrArg Units.val hu).symm)
    refine ⟨r, hr, ?_⟩
    exact calc
      _ = (f.stalkMap (genericPoint C)).hom (sp r) :=
        (generic_stalkMap_commutes f x r).symm
      _ = (f.stalkMap (genericPoint C)).hom (u : X.presheaf.stalk (f (genericPoint C))) :=
        congrArg (f.stalkMap (genericPoint C)).hom he
      _ = _ := (congrArg Units.val hBu).symm
  have hdata : MovedCartierRestrictionData f A 1 B := by
    intro z
    simpa only [one_mul] using hB z
  have hBe : B.Effective := by
    intro z x hx
    obtain ⟨r, _, hr⟩ := hregular z x hx
    exact ⟨(f.stalkMap x).hom r, hr⟩
  refine ⟨B, hdata, hBe, ?_⟩
  ext x
  rw [cartierAtlas_support_eq_on_chart C B x x (hB x).1, Set.mem_preimage,
    cartierAtlas_support_eq_on_chart X A _ (f x) (A.covers (f x)).choose_spec]
  obtain ⟨r, hr, hs⟩ := hregular x x (hB x).1
  rw [rationalUnitAt_regular_iff C x _ _ hs,
    rationalUnitAt_regular_iff X (f x) _ r hr]
  exact not_congr (isUnit_map_iff (f.stalkMap x).hom r)

/-- Final theorem: the well-defined actual local-order Cartier intersection
with a complete normal curve is nonnegative for an effective divisor when
the curve is not contained in its support, and strictly positive if the
curve also meets that support. The proof constructs the regular pullback
and derives its support and orders; no numerical positivity is input. -/
theorem complete_normal_curve_effective_cartier_intersection_signs
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι) (hA : A.Effective)
    (hη : f (genericPoint C) ∉ A.vanishingSupport) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    0 ≤ cartierCurveIntersection hn f A ∧
      ((f ⁻¹' A.vanishingSupport).Nonempty → 0 < cartierCurveIntersection hn f A) := by
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨B, hdata, hBe, hS⟩ := effective_cartier_restriction_with_data f A hA hη
  rw [complete_normal_curve_cartier_intersection_eq_restriction hn hd k c f A 1 B hdata]
  refine ⟨effective_cartierTotalOrder_nonneg C hn B hBe, ?_⟩
  intro hmeet
  exact effective_cartierTotalOrder_pos_of_support C hn B hBe (hS.symm ▸ hmeet)

end
end Negativity
