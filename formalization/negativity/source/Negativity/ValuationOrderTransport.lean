module

public import Negativity.NormalCurveValuations
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- A ring isomorphism inside the same actual fraction field preserves
the signed order of every actual nonzero rational function. The proof
uses numerator/denominator representatives and normalized DVR orders. -/
theorem dvr_rationalOrder_commonField_ringEquiv
    {R S K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]
    (e : R ≃+* S) (he : (algebraMap S K).comp e.toRingHom = algebraMap R K)
    (a : Kˣ) : DvrRationalOrder S K a = DvrRationalOrder R K a := by
  obtain ⟨⟨r, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) (a : K)
  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hsk : algebraMap R K (s : R) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hs
  have hr : r ≠ 0 := by
    intro hz
    exact mul_ne_zero a.ne_zero hsk (by simpa only [hz, map_zero] using h)
  have her : e r ≠ 0 := by simpa only [← e.map_zero] using e.injective.ne hr
  have hes : e (s : R) ≠ 0 := by simpa only [← e.map_zero] using e.injective.ne hs
  have hmap (t : R) : algebraMap S K (e t) = algebraMap R K t :=
    congrArg (fun f : R →+* K ↦ f t) he
  rw [dvr_rationalOrder_represents S K a (e r) (e s) her hes
      (by rw [hmap, hmap]; exact h),
    dvr_fraction_order_ringEquiv e r s,
    dvr_rationalOrder_represents R K a r s hr hs h]

/-- The generic lift's actual local-ring isomorphism preserves all
rational orders at the actual curve center. Its compatibility was proved
from the actual Scheme square in ValuationCenters. -/
theorem normal_curve_valuation_center_order
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (A : ValuationSubring C.functionField) [IsDiscreteValuationRing A]
    (l : Spec (.of A) ⟶ C)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
      C.fromSpecStalk (genericPoint C))
    (hx : Order.coheight (l (IsLocalRing.closedPoint A)) = 1)
    (a : C.functionFieldˣ) :
    DvrRationalOrder A C.functionField a =
      schemeRationalOrder C hn (l (IsLocalRing.closedPoint A)) hx a := by
  let x := l (IsLocalRing.closedPoint A)
  have := hn x
  have := normal_codimensionOne_stalk_isDVR C x hx
  let e : C.presheaf.stalk x ≃+* A := RingEquiv.ofBijective
    (Scheme.stalkClosedPointTo l).hom (valuation_center_stalk_bijective C A l hl)
  exact dvr_rationalOrder_commonField_ringEquiv e
    (valuation_center_stalk_functionField_compat C A l hl) a

/-- Final theorem: a nontrivial DVR place of the actual function field
of a proper normal curve has a unique actual closed-point center, and
every local rational order is preserved by that correspondence. All
geometric center and stalk-isomorphism assertions are constructed. -/
theorem proper_normal_curve_valuation_order_correspondence
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b]
    (A : ValuationSubring C.functionField) [IsDiscreteValuationRing A] (hA : A ≠ ⊤)
    (hk : ∀ c : k, curveFunctionFieldBaseMap C k b c ∈ A) :
    ∃ l : Spec (.of A) ⟶ C,
      (Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
        C.fromSpecStalk (genericPoint C) ∧
      l ≫ b = Spec.map (CommRingCat.ofHom
        ((curveFunctionFieldBaseMap C k b).codRestrict A.toSubring hk))) ∧
      ∃ hx : Order.coheight (l (IsLocalRing.closedPoint A)) = 1,
        IsClosed ({l (IsLocalRing.closedPoint A)} : Set C) ∧
        (∀ a : C.functionFieldˣ,
          DvrRationalOrder A C.functionField a =
            schemeRationalOrder C hn (l (IsLocalRing.closedPoint A)) hx a) ∧
        ∀ l' : Spec (.of A) ⟶ C,
          Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l' =
            C.fromSpecStalk (genericPoint C) → l' = l := by
  obtain ⟨l, hl, huniq⟩ := proper_functionField_valuation_unique_lift C k b A hk
  have hx := nontrivial_valuation_center_coheight_one C hd A hA l hl.1
  exact ⟨l, hl, hx, curve_coheight_one_isClosed C hd _ hx,
    normal_curve_valuation_center_order C hn A l hl.1 hx,
    fun l' hl' ↦ huniq l' ⟨hl', valuation_generic_lift_over_base C k b A hk l' hl'⟩⟩

end Negativity
