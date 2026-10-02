module

public import Negativity.LocalGeometry
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual map from the ground field to the function field, obtained
from the generic point of the given structure morphism. -/
noncomputable def curveFunctionFieldBaseMap (C : Scheme.{u}) [IsIntegral C]
    (k : Type u) [Field k] (b : C ⟶ Spec (.of k)) : k →+* C.functionField :=
  (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ b)).hom

theorem curveFunctionFieldBaseMap_spec (C : Scheme.{u}) [IsIntegral C]
    (k : Type u) [Field k] (b : C ⟶ Spec (.of k)) :
    Spec.map (CommRingCat.ofHom (curveFunctionFieldBaseMap C k b)) =
      C.fromSpecStalk (genericPoint C) ≫ b := by
  exact Spec.map_preimage _

/-- A local inclusion from a valuation ring into a subring of the same
fraction field is an isomorphism. No finite-extension or separability
assumption enters this local algebra lemma. -/
theorem local_valuation_fractionRing_bijective
    (R S K : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [IsDomain S] [Field K] [Algebra R S] [Algebra S K]
    [Algebra R K] [IsScalarTower R S K] [IsFractionRing R K]
    [IsFractionRing S K] [IsLocalHom (algebraMap R S)] :
    Function.Bijective (algebraMap R S) := by
  refine ⟨?_, ?_⟩
  · intro r t h
    apply IsFractionRing.injective R K
    simpa only [IsScalarTower.algebraMap_apply R S K] using
      congrArg (algebraMap S K) h
  · intro s
    by_cases hs : s = 0
    · exact ⟨0, by simp [hs]⟩
    have hsK : algebraMap S K s ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective S K).ne hs
    obtain ⟨r, hr⟩ | ⟨r, hr⟩ :=
      ValuationRing.isInteger_or_isInteger R (algebraMap S K s)
    · exact ⟨r, (IsFractionRing.injective S K)
        (by simpa only [IsScalarTower.algebraMap_apply R S K] using hr)⟩
    · have hmul : algebraMap R S r * s = 1 := by
        apply IsFractionRing.injective S K
        simp only [map_mul, map_one, ← IsScalarTower.algebraMap_apply R S K,
          hr, inv_mul_cancel₀ hsK]
      have hu : IsUnit r := isUnit_of_map_unit (algebraMap R S) r
        (IsUnit.of_mul_eq_one _ hmul)
      refine ⟨↑(hu.unit⁻¹), ?_⟩
      apply mul_left_cancel₀ ((hu.map (algebraMap R S)).ne_zero)
      calc
        algebraMap R S r * algebraMap R S (↑(hu.unit⁻¹)) = 1 := by
          have he : r * ↑(hu.unit⁻¹) = 1 := by
            simpa only [Units.val_mul, hu.unit_spec, Units.val_one] using
              congrArg (fun v : Rˣ ↦ (v : R)) (mul_inv_cancel hu.unit)
          simpa only [map_mul, map_one] using congrArg (algebraMap R S) he
        _ = algebraMap R S r * s := hmul.symm

/-- A map extending the actual generic point automatically respects the
ground field. The equality follows by injectivity of A into the function
field, so it need not be required again as an extra square assumption. -/
theorem valuation_generic_lift_over_base (C : Scheme.{u}) [IsIntegral C]
    (k : Type u) [Field k] (b : C ⟶ Spec (.of k))
    (A : ValuationSubring C.functionField)
    (hk : ∀ c : k, curveFunctionFieldBaseMap C k b c ∈ A)
    (l : Spec (.of A) ⟶ C)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
      C.fromSpecStalk (genericPoint C)) :
    l ≫ b = Spec.map (CommRingCat.ofHom
      ((curveFunctionFieldBaseMap C k b).codRestrict A.toSubring hk)) := by
  let f : k →+* A := (Spec.preimage (l ≫ b)).hom
  have hpre : Spec.map (CommRingCat.ofHom f) = l ≫ b := Spec.map_preimage _
  have hm : Spec.map (CommRingCat.ofHom ((algebraMap A C.functionField).comp f)) =
      Spec.map (CommRingCat.ofHom (curveFunctionFieldBaseMap C k b)) := by
    change Spec.map ((CommRingCat.ofHom f) ≫
      CommRingCat.ofHom (algebraMap A C.functionField)) = _
    rw [Spec.map_comp, hpre, ← Category.assoc, hl, curveFunctionFieldBaseMap_spec]
  have he := congrArg CommRingCat.Hom.hom (Spec.map_injective hm)
  have hf : f = (curveFunctionFieldBaseMap C k b).codRestrict A.toSubring hk := by
    ext c
    exact congrArg (fun g : k →+* C.functionField ↦ g c) he
  rw [← hpre, hf]

/-- Hartshorne I.6: a valuation subring of the actual function field,
containing the actual ground-field constants, has a unique map to a proper
integral scheme extending its generic point. The square is constructed,
not supplied as an additional existence hypothesis. Its closed point is
the unique valuation center. -/
theorem proper_functionField_valuation_unique_lift
    (C : Scheme.{u}) [IsIntegral C] (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b]
    (A : ValuationSubring C.functionField)
    (hk : ∀ c : k, curveFunctionFieldBaseMap C k b c ∈ A) :
    ∃! l : Spec (.of A) ⟶ C,
      Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
        C.fromSpecStalk (genericPoint C) ∧
      l ≫ b = Spec.map (CommRingCat.ofHom
        ((curveFunctionFieldBaseMap C k b).codRestrict A.toSubring hk)) := by
  let constants : k →+* A :=
    (curveFunctionFieldBaseMap C k b).codRestrict A.toSubring hk
  let bottom := Spec.map (CommRingCat.ofHom constants)
  have hw : C.fromSpecStalk (genericPoint C) ≫ b =
      Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ bottom := by
    rw [← curveFunctionFieldBaseMap_spec C k b, ← Spec.map_comp]
    rfl
  let square : ValuativeCommSq b := {
    R := A, K := C.functionField, i₁ := C.fromSpecStalk (genericPoint C),
    i₂ := bottom, commSq := ⟨hw⟩ }
  have hp : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓
      @LocallyOfFiniteType) b := by
    rw [← IsProper.eq_valuativeCriterion]
    exact inferInstance
  obtain ⟨lift⟩ := ((ValuativeCriterion.existence hp.1.1.1) square).exists_lift
  refine ⟨lift.l, ⟨lift.fac_left, lift.fac_right⟩, ?_⟩
  intro l hl
  let other : square.commSq.LiftStruct := ⟨l, hl.1, hl.2⟩
  have : Subsingleton square.commSq.LiftStruct := proper_valuative_lift_unique b square
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim other lift)

/-- The center's local map and the valuation inclusion induce the same
actual embedding into the function field. This is deduced from the
generic-point equality, not introduced as a compatibility input. -/
theorem valuation_center_stalk_functionField_compat
    (C : Scheme.{u}) [IsIntegral C] (A : ValuationSubring C.functionField)
    (l : Spec (.of A) ⟶ C)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
      C.fromSpecStalk (genericPoint C)) :
    (algebraMap A C.functionField).comp (Scheme.stalkClosedPointTo l).hom =
      algebraMap (C.presheaf.stalk (l (IsLocalRing.closedPoint A))) C.functionField := by
  let x := l (IsLocalRing.closedPoint A)
  have hg : Spec.map (CommRingCat.ofHom
      (algebraMap (C.presheaf.stalk x) C.functionField)) ≫ C.fromSpecStalk x =
      C.fromSpecStalk (genericPoint C) :=
    C.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C).specializes trivial)
  have hm : Spec.map (CommRingCat.ofHom
      ((algebraMap A C.functionField).comp (Scheme.stalkClosedPointTo l).hom)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (C.presheaf.stalk x) C.functionField)) := by
    rw [← cancel_mono (C.fromSpecStalk x)]
    change Spec.map ((Scheme.stalkClosedPointTo l) ≫
        CommRingCat.ofHom (algebraMap A C.functionField)) ≫ C.fromSpecStalk x = _
    rw [Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl, hg]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hm)

/-- If the center's local ring is a valuation ring (in particular a normal
curve's closed-point DVR), its actual local map onto the given valuation
ring is bijective. -/
theorem valuation_center_stalk_bijective
    (C : Scheme.{u}) [IsIntegral C] (A : ValuationSubring C.functionField)
    (l : Spec (.of A) ⟶ C)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
      C.fromSpecStalk (genericPoint C))
    [ValuationRing (C.presheaf.stalk (l (IsLocalRing.closedPoint A)))] :
    Function.Bijective (Scheme.stalkClosedPointTo l).hom := by
  let R := C.presheaf.stalk (l (IsLocalRing.closedPoint A))
  let : Algebra R A := (Scheme.stalkClosedPointTo l).hom.toAlgebra
  have : IsLocalHom (algebraMap R A) := by
    change IsLocalHom (Scheme.stalkClosedPointTo l).hom
    infer_instance
  have : IsScalarTower R A C.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (valuation_center_stalk_functionField_compat C A l hl).symm
  exact local_valuation_fractionRing_bijective R A C.functionField

/-- Every stalk of a locally Noetherian normal integral scheme of dimension
at most one is a valuation ring: it is either a field or a DVR. -/
theorem normal_curve_stalk_isValuation (C : Scheme.{u}) [IsIntegral C]
    [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (x : C) : ValuationRing (C.presheaf.stalk x) := by
  have hx : Order.coheight x ≤ 1 :=
    WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans hd)
  by_cases hx0 : Order.coheight x = 0
  · have : Ring.KrullDimLE 0 (C.presheaf.stalk x) :=
      krullDimLE_of_coheight_le hx0.le
    let : Field (C.presheaf.stalk x) := Ring.KrullDimLE.isField_of_isDomain.toField
    infer_instance
  · have hx1 : Order.coheight x = 1 :=
      le_antisymm hx (Order.one_le_iff_ne_zero.mpr hx0)
    have := hn x
    have := normal_one_dimensional_local_isDVR (C.presheaf.stalk x)
      (by rw [ringKrullDim_stalk_eq_coheight, hx1]; rfl)
    infer_instance

/-- A nontrivial valuation has a codimension-one center on an integral
scheme of dimension at most one. It cannot have the generic-point stalk,
since that field would force every function-field element into A. -/
theorem nontrivial_valuation_center_coheight_one
    (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C ≤ 1)
    (A : ValuationSubring C.functionField) (hA : A ≠ ⊤)
    (l : Spec (.of A) ⟶ C)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
      C.fromSpecStalk (genericPoint C)) :
    Order.coheight (l (IsLocalRing.closedPoint A)) = 1 := by
  let x := l (IsLocalRing.closedPoint A)
  have hx : Order.coheight x ≤ 1 :=
    WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans hd)
  have hx0 : Order.coheight x ≠ 0 := by
    intro hzero
    let R := C.presheaf.stalk x
    have : Ring.KrullDimLE 0 R := krullDimLE_of_coheight_le hzero.le
    have hsur : Function.Surjective (algebraMap R C.functionField) :=
      (IsField.localization_map_bijective
        (M := nonZeroDivisors R) (by simp)
        Ring.KrullDimLE.isField_of_isDomain).2
    apply hA
    apply top_unique
    intro a _
    obtain ⟨r, hr⟩ := hsur a
    have he := congrArg (fun f : R →+* C.functionField ↦ f r)
      (valuation_center_stalk_functionField_compat C A l hl)
    rw [hr] at he
    rw [← he]
    exact ((Scheme.stalkClosedPointTo l).hom r).2
  exact le_antisymm hx (Order.one_le_iff_ne_zero.mpr hx0)

/-- Codimension-one points on a scheme of dimension at most one are
actually closed points, by the specialization order. -/
theorem curve_coheight_one_isClosed (C : Scheme.{u})
    (hd : Order.krullDim C ≤ 1) (x : C) (hx : Order.coheight x = 1) :
    IsClosed ({x} : Set C) := by
  rw [← closure_eq_iff_isClosed]
  apply Set.Subset.antisymm ?_ subset_closure
  intro y hy
  have hyx : y ≤ x := (specializes_iff_mem_closure).mpr hy
  have hybound : Order.coheight y ≤ 1 :=
    WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim y).trans hd)
  apply Set.mem_singleton_iff.mpr
  by_contra hne
  have hlt := (Order.coheight_le_coe_iff (n := 1)).mp hybound x
    (show y < x from ⟨hyx, fun hxy ↦ hne ((hxy.antisymm hyx).eq)⟩)
  rw [hx] at hlt
  exact (lt_irrefl _ hlt)

/-- Final theorem of this module: the valuation-center correspondence in
the direction needed for Hartshorne I.6. Properness constructs the unique
center map; normality and dimension identify its actual stalk with the
valuation subring of the actual function field. No center, local-isomorphism
or fraction-field compatibility assertion is assumed. -/
theorem proper_normal_curve_unique_valuation_center_iso
    (C : Scheme.{u}) [IsIntegral C] [IsLocallyNoetherian C]
    (hn : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (hd : Order.krullDim C ≤ 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [IsProper b]
    (A : ValuationSubring C.functionField)
    (hk : ∀ c : k, curveFunctionFieldBaseMap C k b c ∈ A) :
    ∃! l : Spec (.of A) ⟶ C,
      (Spec.map (CommRingCat.ofHom (algebraMap A C.functionField)) ≫ l =
        C.fromSpecStalk (genericPoint C) ∧
      l ≫ b = Spec.map (CommRingCat.ofHom
        ((curveFunctionFieldBaseMap C k b).codRestrict A.toSubring hk))) ∧
      Function.Bijective (Scheme.stalkClosedPointTo l).hom ∧
      (A ≠ ⊤ → IsClosed ({l (IsLocalRing.closedPoint A)} : Set C)) := by
  obtain ⟨l, hl, huniq⟩ := proper_functionField_valuation_unique_lift C k b A hk
  have := normal_curve_stalk_isValuation C hn hd (l (IsLocalRing.closedPoint A))
  exact ⟨l, ⟨hl, valuation_center_stalk_bijective C A l hl.1,
    fun hA ↦ curve_coheight_one_isClosed C hd _
      (nontrivial_valuation_center_coheight_one C hd A hA l hl.1)⟩,
    fun other ho ↦ huniq other ho.1⟩

end Negativity
