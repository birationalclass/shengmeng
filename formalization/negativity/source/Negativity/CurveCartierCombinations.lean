module

public import Negativity.CartierCurveIntersection
public import Negativity.CartierCombinations
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Change the target chart of a genuine moved restriction at an actual
source point. The discrepancy is an actual unit in the source stalk,
obtained from the target Cartier transition and the Scheme stalk square. -/
theorem moved_restriction_equation_on_chart
    {C X : Scheme} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) {ι : Type*} (A : CartierAtlas X ι)
    (a : X.functionFieldˣ) (B : CartierAtlas C C)
    (hB : MovedCartierRestrictionData f A a B)
    (x : C) (i : ι) (hi : f x ∈ A.chart i) :
    ∃ (u : (X.presheaf.stalk (f (genericPoint C)))ˣ) (v : (C.presheaf.stalk x)ˣ),
      Units.map (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom u =
        a * A.equation i ∧
      Units.map (f.stalkMap (genericPoint C)).hom.toMonoidHom u =
        Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom v * B.equation x := by
  obtain ⟨u₀, hu₀, hBu₀⟩ := (hB x).2.2
  obtain ⟨w, hw⟩ := A.transition _ i (f x) (A.covers (f x)).choose_spec hi
  let sp : X.presheaf.stalk (f x) →+* X.presheaf.stalk (f (genericPoint C)) :=
    (X.presheaf.stalkSpecializes
      (f.base.hom.map_specializes ((genericPoint_spec C).specializes trivial))).hom
  have hs : Units.map (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom
      (Units.map sp.toMonoidHom w) =
      Units.map (algebraMap (X.presheaf.stalk (f x)) X.functionField).toMonoidHom w := by
    apply Units.ext
    exact stalkSpecialization_functionField X _ _ _ (w : X.presheaf.stalk (f x))
  have hp : Units.map (f.stalkMap (genericPoint C)).hom.toMonoidHom (Units.map sp.toMonoidHom w) =
      Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom
        (Units.map (f.stalkMap x).hom.toMonoidHom w) := by
    apply Units.ext
    exact generic_stalkMap_commutes f x (w : X.presheaf.stalk (f x))
  refine ⟨Units.map sp.toMonoidHom w * u₀, Units.map (f.stalkMap x).hom.toMonoidHom w, ?_, ?_⟩
  · rw [map_mul, hs, hu₀, mul_left_comm]
    exact congrArg (fun b => a * b) hw
  · rw [map_mul, hp, hBu₀]

/-- The product of actual moved restriction units gives a genuine generic
unit for the actual integral Cartier combination. At each actual source
point it differs from the product of source equations only by a stalk unit. -/
theorem integral_combination_moved_local_units
    {C X : Scheme} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (n : τ → ℤ)
    (a : τ → X.functionFieldˣ) (B : τ → CartierAtlas C C)
    (hB : ∀ t, MovedCartierRestrictionData f (A t) (a t) (B t))
    (D : CartierAtlas X X)
    (hD : ∀ z : X, z ∈ D.chart z ∧
      (∀ t, D.chart z ≤ (A t).chart ((A t).covers z).choose) ∧
      D.equation z = ∏ t, (A t).equation ((A t).covers z).choose ^ n t)
    (x : C) :
    ∃ (u : (X.presheaf.stalk (f (genericPoint C)))ˣ) (v : (C.presheaf.stalk x)ˣ),
      Units.map (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom u =
        (∏ t, a t ^ n t) * D.equation (D.covers (f x)).choose ∧
      Units.map (f.stalkMap (genericPoint C)).hom.toMonoidHom u =
        Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom v *
          ∏ t, (B t).equation x ^ n t := by
  classical
  let j := (D.covers (f x)).choose
  have hi (t : τ) : f x ∈ (A t).chart ((A t).covers j).choose :=
    (hD j).2.1 t (D.covers (f x)).choose_spec
  choose u v hu hv using fun t => moved_restriction_equation_on_chart f (A t) (a t)
    (B t) (hB t) x _ (hi t)
  refine ⟨∏ t, u t ^ n t, ∏ t, v t ^ n t, ?_, ?_⟩
  · simp only [map_prod, map_zpow, hu, mul_zpow, Finset.prod_mul_distrib]
    rw [(hD j).2.2]
  · simp only [map_prod, map_zpow, hv, mul_zpow, Finset.prod_mul_distrib]

/-- Final theorem: construct an actual integral combination of ambient
Cartier atlases, with its actual affine charts and product equations, and
prove that the choice-independent complete-curve intersection is additive
with those integer coefficients. Actual Cartier transition units account
for all chart changes. No numerical linearity identity is assumed. -/
theorem exists_complete_curve_cartier_intersection_integralCombination
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C = 1) (k : Type u) [Field k] [IsAlgClosed k]
    (c : C ⟶ Spec (.of k)) [IsProper c]
    (f : C ⟶ X) {ι τ : Type*} [Fintype τ]
    (A : τ → CartierAtlas X ι) (n : τ → ℤ) :
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
    ∃ D : CartierAtlas X X,
      (∀ z : X, z ∈ D.chart z ∧
        (∀ t, D.chart z ≤ (A t).chart ((A t).covers z).choose) ∧
        D.equation z = ∏ t, (A t).equation ((A t).covers z).choose ^ n t) ∧
      cartierCurveIntersection hn f D = ∑ t, n t * cartierCurveIntersection hn f (A t) := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨D, hD⟩ := exists_cartierAtlas_integralCombination X A n
  let R (t : τ) := movedCartierCurveRestriction f (A t)
  let a (t : τ) := (R t).move
  let B (t : τ) := (R t).atlas
  have hB (t : τ) : MovedCartierRestrictionData f (A t) (a t) (B t) := (R t).data
  let aD := ∏ t, a t ^ n t
  have hη : f (genericPoint C) ∉ (D.rationalTwist aD).vanishingSupport := by
    intro h
    apply h
    obtain ⟨u, _, hu, _⟩ := integral_combination_moved_local_units f A n a B hB D hD (genericPoint C)
    exact ⟨u, hu⟩
  obtain ⟨E, hE⟩ := exists_cartierAtlas_nondominant_pullback f (D.rationalTwist aD) hη
  have hdata : MovedCartierRestrictionData f D aD E := hE
  have hc (x : C) : E.coefficient hn x = ∑ t, n t * (B t).coefficient hn x := by
    by_cases hx : Order.coheight x = 1
    · obtain ⟨u, v, hu, hv⟩ := integral_combination_moved_local_units f A n a B hB D hD x
      obtain ⟨uE, huE, hEuE⟩ := (hE x).2.2
      have huEq : uE = u := by
        apply Units.map_injective
          (f := (algebraMap (X.presheaf.stalk (f (genericPoint C))) X.functionField).toMonoidHom)
          (IsFractionRing.injective _ _)
        exact huE.trans hu.symm
      have heq : E.equation x =
          Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom v *
            ∏ t, (B t).equation x ^ n t := by
        rw [hEuE, huEq]
        exact hv
      rw [cartierAtlas_coefficient_eq C hn E x x hx (hE x).1, heq]
      have := hn x
      have := normal_codimensionOne_stalk_isDVR C x hx
      unfold schemeRationalOrder
      dsimp only
      calc
        DvrRationalOrder (C.presheaf.stalk x) C.functionField
            (Units.map (algebraMap (C.presheaf.stalk x) C.functionField).toMonoidHom v *
              ∏ t, (B t).equation x ^ n t) =
            DvrRationalOrder (C.presheaf.stalk x) C.functionField
              (∏ t, (B t).equation x ^ n t) :=
          dvr_rationalOrder_unit_transition (C.presheaf.stalk x) C.functionField v _
        _ = ∑ t, n t * (B t).coefficient hn x := ?_
      rw [dvr_rationalOrder_prod]
      apply Finset.sum_congr rfl
      intro t _
      rw [dvr_rationalOrder_zpow, cartierAtlas_coefficient_eq C hn (B t) x x hx (hB t x).1]
      rfl
    · simp [CartierAtlas.coefficient, hx]
  have hs : cartierOrderDivisor C hn E = ∑ t, n t • cartierOrderDivisor C hn (B t) := by
    ext x
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, cartierOrderDivisor_apply, zsmul_eq_mul]
    exact hc x
  refine ⟨D, hD, ?_⟩
  rw [complete_normal_curve_cartier_intersection_eq_restriction hn hd k c f D aD E hdata]
  change (cartierOrderDivisor C hn E).degree = _
  rw [hs, map_sum]
  simp only [map_zsmul, zsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (fun z : ℤ => n t * z)
    (complete_normal_curve_cartier_intersection_eq_restriction hn hd k c f (A t) (a t) (B t) (hB t)).symm

end
end Negativity
