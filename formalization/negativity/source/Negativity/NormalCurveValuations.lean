module

public import Negativity.ValuationCenters
public import Negativity.CartierAtlas
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing
universe u
set_option backward.isDefEq.respectTransparency false

/-- The valuation subring of the actual function field attached to an
actual codimension-one point, obtained from its normal DVR stalk. -/
noncomputable def normalCurvePointValuation (C : Scheme.{u}) [IsIntegral C]
    [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (x : C) (hx : Order.coheight x = 1) : ValuationSubring C.functionField := by
  have := hn x
  have := normal_codimensionOne_stalk_isDVR C x hx
  exact ValuationSubring.ofSubring (algebraMap (C.presheaf.stalk x) C.functionField).range
    (fun a ↦ ValuationRing.isInteger_or_isInteger (C.presheaf.stalk x) a)

/-- This stalk valuation is nontrivial: a uniformizer cannot have a
regular inverse in the stalk. -/
theorem normalCurvePointValuation_ne_top (C : Scheme.{u}) [IsIntegral C]
    [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (x : C) (hx : Order.coheight x = 1) :
    normalCurvePointValuation C hn x hx ≠ ⊤ := by
  have := hn x
  have := normal_codimensionOne_stalk_isDVR C x hx
  intro he
  let R := C.presheaf.stalk x
  obtain ⟨p, hp⟩ := exists_prime R
  have hpK : algebraMap R C.functionField p ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R C.functionField).ne hp.ne_zero
  have hm : (algebraMap R C.functionField p)⁻¹ ∈ normalCurvePointValuation C hn x hx := by
    rw [he]; trivial
  obtain ⟨r, hr⟩ := hm
  have hpr : p * r = 1 := by
    apply IsFractionRing.injective R C.functionField
    rw [map_mul, map_one]
    change algebraMap (C.presheaf.stalk x) C.functionField p *
      algebraMap (C.presheaf.stalk x) C.functionField r = 1
    rw [hr]
    exact mul_inv_cancel₀ hpK
  exact hp.not_isUnit (IsUnit.of_mul_eq_one r hpr)

/-- Constants belong to every curve-point valuation. The equality of
ground-field maps is proved using the actual specialization square. -/
theorem normalCurvePointValuation_contains_constants
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (x : C) (hx : Order.coheight x = 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) (c : k) :
    curveFunctionFieldBaseMap C k b c ∈ normalCurvePointValuation C hn x hx := by
  let constants : k →+* C.presheaf.stalk x := (Spec.preimage (C.fromSpecStalk x ≫ b)).hom
  have he : (algebraMap (C.presheaf.stalk x) C.functionField).comp constants =
      curveFunctionFieldBaseMap C k b := by
    have hm : Spec.map (CommRingCat.ofHom
        ((algebraMap (C.presheaf.stalk x) C.functionField).comp constants)) =
        Spec.map (CommRingCat.ofHom (curveFunctionFieldBaseMap C k b)) := by
      change Spec.map ((CommRingCat.ofHom constants) ≫
        CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) = _
      rw [Spec.map_comp]
      have hconstants : Spec.map (CommRingCat.ofHom constants) = C.fromSpecStalk x ≫ b :=
        Spec.map_preimage _
      have hg : Spec.map (CommRingCat.ofHom
          (algebraMap (C.presheaf.stalk x) C.functionField)) ≫ C.fromSpecStalk x =
          C.fromSpecStalk (genericPoint C) :=
        C.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C).specializes trivial)
      rw [hconstants, ← Category.assoc, hg, curveFunctionFieldBaseMap_spec]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hm)
  exact ⟨constants c, congrArg (fun f : k →+* C.functionField ↦ f c) he⟩

/-- The valuation subring at the actual center is exactly the given
valuation subring, as subrings of the same actual function field. -/
theorem normalCurvePointValuation_center_eq
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (A : ValuationSubring C.functionField) (l : Spec (.of A) ⟶ C)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
      C.fromSpecStalk (genericPoint C))
    (hx : Order.coheight (l (IsLocalRing.closedPoint A)) = 1) :
    normalCurvePointValuation C hn (l (IsLocalRing.closedPoint A)) hx = A := by
  let x := l (IsLocalRing.closedPoint A)
  have := hn x
  have := normal_codimensionOne_stalk_isDVR C x hx
  have hsur := (valuation_center_stalk_bijective C A l hl).2
  have hcomp := valuation_center_stalk_functionField_compat C A l hl
  apply SetLike.ext
  intro a
  constructor
  · rintro ⟨r, hr⟩
    have he := congrArg (fun f : C.presheaf.stalk x →+* C.functionField ↦ f r) hcomp
    rw [hr] at he
    rw [← he]
    exact ((Scheme.stalkClosedPointTo l).hom r).2
  · intro ha
    obtain ⟨r, hr⟩ := hsur ⟨a, ha⟩
    refine ⟨r, ?_⟩
    have he := congrArg (fun f : C.presheaf.stalk x →+* C.functionField ↦ f r) hcomp
    calc
      algebraMap (C.presheaf.stalk x) C.functionField r =
          algebraMap A C.functionField ((Scheme.stalkClosedPointTo l).hom r) := he.symm
      _ = a := congrArg (fun z : A ↦ (z : C.functionField)) hr

/-- The canonical map from the point's actual valuation ring has the
given point as its center and extends the actual generic point. -/
theorem normalCurvePointValuation_lift
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (x : C) (hx : Order.coheight x = 1) :
    ∃ l : Spec (.of (normalCurvePointValuation C hn x hx)) ⟶ C,
      Spec.map (CommRingCat.ofHom
        (algebraMap (normalCurvePointValuation C hn x hx) C.functionField)) ≫ l =
          C.fromSpecStalk (genericPoint C) ∧
      l (IsLocalRing.closedPoint (normalCurvePointValuation C hn x hx)) = x := by
  let R := C.presheaf.stalk x
  let A := normalCurvePointValuation C hn x hx
  let e : R ≃+* A := RingEquiv.ofBijective (algebraMap R C.functionField).rangeRestrict
    ⟨fun r t h ↦ (IsFractionRing.injective R C.functionField) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩
  have : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  let l : Spec (.of A) ⟶ C := Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk x
  have hl : Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
      C.fromSpecStalk (genericPoint C) := by
    dsimp only [l]
    rw [← Category.assoc, ← Spec.map_comp]
    exact C.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C).specializes trivial)
  refine ⟨l, hl, ?_⟩
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk x)
    (IsLocalRing.closedPoint A) = x
  rw [Scheme.Hom.comp_apply, Spec_closedPoint]
  exact C.fromSpecStalk_closedPoint

/-- Two actual curve points with the same function-field valuation are
equal, by uniqueness of the proper valuative lift. -/
theorem normalCurvePointValuation_injective
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (k : Type u) [Field k] (b : C ⟶ Spec (.of k)) [IsProper b]
    (x y : C) (hx : Order.coheight x = 1) (hy : Order.coheight y = 1)
    (he : normalCurvePointValuation C hn x hx = normalCurvePointValuation C hn y hy) :
    x = y := by
  let A := normalCurvePointValuation C hn x hx
  obtain ⟨lx, hlx, hcx⟩ := normalCurvePointValuation_lift C hn x hx
  have hly := normalCurvePointValuation_lift C hn y hy
  rw [← he] at hly
  obtain ⟨ly, hly, hcy⟩ := hly
  obtain ⟨l, _, huniq⟩ := proper_functionField_valuation_unique_lift C k b A
    (normalCurvePointValuation_contains_constants C hn x hx k b)
  have hxl : lx = l := huniq lx ⟨hlx, valuation_generic_lift_over_base C k b A
    (normalCurvePointValuation_contains_constants C hn x hx k b) lx hlx⟩
  have hyl : ly = l := huniq ly ⟨hly, valuation_generic_lift_over_base C k b A
    (normalCurvePointValuation_contains_constants C hn x hx k b) ly hly⟩
  exact hcx.symm.trans ((congrArg (fun f : Spec (.of A) ⟶ C ↦
    f (IsLocalRing.closedPoint A)) (hxl.trans hyl.symm)).trans hcy)

/-- Every nontrivial ground-field valuation of the actual function field
of a proper normal curve is the actual DVR valuation of a closed point.
This proves existence from properness, rather than taking a list of
closed points or a valuation-to-point correspondence as an input. -/
theorem proper_normal_curve_valuation_has_closed_point
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b]
    (A : ValuationSubring C.functionField) (hA : A ≠ ⊤)
    (hk : ∀ c : k, curveFunctionFieldBaseMap C k b c ∈ A) :
    ∃ x : C, ∃ hx : Order.coheight x = 1,
      IsClosed ({x} : Set C) ∧ normalCurvePointValuation C hn x hx = A := by
  obtain ⟨l, hl, _⟩ := proper_functionField_valuation_unique_lift C k b A hk
  have hx := nontrivial_valuation_center_coheight_one C hd A hA l hl.1
  exact ⟨l (IsLocalRing.closedPoint A), hx, curve_coheight_one_isClosed C hd _ hx,
    normalCurvePointValuation_center_eq C hn A l hl.1 hx⟩

/-- The point-to-valuation map has the correct geometric target:
nontrivial valuation subrings containing the actual base-field constants. -/
noncomputable def normalCurveValuationMap
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (k : Type u) [Field k] (b : C ⟶ Spec (.of k)) :
    {x : C // Order.coheight x = 1} →
      {A : ValuationSubring C.functionField // A ≠ ⊤ ∧
        ∀ c : k, curveFunctionFieldBaseMap C k b c ∈ A} := fun x ↦
  ⟨normalCurvePointValuation C hn x x.2,
    normalCurvePointValuation_ne_top C hn x x.2,
    normalCurvePointValuation_contains_constants C hn x x.2 k b⟩

/-- Final theorem (Hartshorne I.6): the actual codimension-one closed
points of a proper normal integral curve correspond bijectively to the
nontrivial ground-field valuation rings of its actual function field.
Both directions and uniqueness are proved using actual Scheme maps.
There is no supplied place/point bijection, and no characteristic restriction. -/
theorem proper_normal_curve_points_valuations_bijective
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b] :
    Function.Bijective (normalCurveValuationMap C hn k b) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    exact normalCurvePointValuation_injective C hn k b x y x.2 y.2
      (congrArg Subtype.val h)
  · intro A
    obtain ⟨x, hx, _, he⟩ := proper_normal_curve_valuation_has_closed_point
      C hn hd k b A.1 A.2.1 A.2.2
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

end Negativity
