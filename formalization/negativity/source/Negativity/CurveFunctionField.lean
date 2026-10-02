module

public import Negativity.AffineCurveFunctionField
public import Negativity.SeparatingParameter
public import Negativity.ValuationCenters
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

theorem curve_affine_chart_dimension (C : Scheme.{u}) [IsIntegral C]
    (hd : Order.krullDim C ≤ 1) (U : C.Opens) (hU : IsAffineOpen U) :
    Ring.KrullDimLE 1 Γ(C, U) := by
  rw [Ring.krullDimLE_iff, ringKrullDim, Order.krullDim_eq_iSup_height]
  apply iSup_le
  intro p
  rw [← PrimeSpectrum.height_eq_orderHeight, idealHeight_eq_coheight]
  rw [← coheight_eq_of_isOpenImmersion hU.fromSpec]
  exact (Order.coheight_le_krullDim (hU.fromSpec p)).trans hd

theorem curve_affine_chart_not_field (C : Scheme.{u}) [IsIntegral C]
    (U : C.Opens) (hU : IsAffineOpen U) (x : C) (hxU : x ∈ U)
    (hx : Order.coheight x = 1) : ¬ IsField Γ(C, U) := by
  intro hf
  let := hf.toField
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hp : p.asIdeal.height = 1 := by
    rw [idealHeight_eq_coheight]
    change Order.coheight (hU.isoSpec.hom ⟨x, hxU⟩) = 1
    rw [coheight_eq_of_isOpenImmersion]
    exact (coheight_eq_of_isOpenImmersion (f := U.ι)).symm.trans hx
  have hle := Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
  rw [ringKrullDim_eq_zero_of_field, hp] at hle
  norm_num at hle

/-- Actual affine section constants agree with the actual generic-stalk
constants after passing to the function field. -/
theorem curve_affine_constants_compatible (C : Scheme.{u}) [IsIntegral C]
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (k : Type u) [Field k] (b : C ⟶ Spec (.of k)) :
    (C.germToFunctionField U).hom.comp (Spec.preimage (hU.fromSpec ≫ b)).hom =
      curveFunctionFieldBaseMap C k b := by
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  change Spec.map (Spec.preimage (hU.fromSpec ≫ b) ≫ C.germToFunctionField U) = _
  rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc]
  change (Spec.map (C.presheaf.germ U (genericPoint C) _) ≫ hU.fromSpec) ≫ b = _
  change hU.fromSpecStalk _ ≫ b = _
  rw [hU.fromSpecStalk_eq_fromSpecStalk]
  exact (curveFunctionFieldBaseMap_spec C k b).symm

theorem curve_functionField_properties_of_closed_point
    (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C ≤ 1)
    (x : C) (hx : Order.coheight x = 1) (k : Type u) [Field k]
    (b : C ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    [Algebra k C.functionField]
    (hbase : algebraMap k C.functionField = curveFunctionFieldBaseMap C k b) :
    Algebra.EssFiniteType k C.functionField ∧ Algebra.trdeg k C.functionField = 1 := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let R := Γ(C, U)
  let c : k →+* R := (Spec.preimage (hU.fromSpec ≫ b)).hom
  let : Algebra k R := c.toAlgebra
  have hc : c.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.FiniteType k R := hc
  have : Ring.KrullDimLE 1 R := curve_affine_chart_dimension C hd U hU
  have : IsFractionRing R C.functionField := functionField_isFractionRing_of_isAffineOpen C U hU
  have : IsScalarTower k R C.functionField := IsScalarTower.of_algebraMap_eq' (by
    rw [hbase]
    exact (curve_affine_constants_compatible C U hU k b).symm)
  exact affine_curve_fractionField_finiteType_trdeg_one k R C.functionField
    (curve_affine_chart_not_field C U hU x hxU hx)

/-- A genuinely one-dimensional integral scheme has a codimension-one
point; this is derived from dimension, not supplied as a point-list input. -/
theorem curve_exists_coheight_one (C : Scheme.{u}) [IsIntegral C]
    (hd : Order.krullDim C = 1) : ∃ x : C, Order.coheight x = 1 := by
  by_contra h
  have hall : ∀ x : C, Order.coheight x = 0 := by
    intro x
    have hxle : Order.coheight x ≤ 1 :=
      WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans hd.le)
    have hxne : Order.coheight x ≠ 1 := fun hx => h ⟨x, hx⟩
    exact Order.lt_one_iff.mp (lt_of_le_of_ne hxle hxne)
  have hz : Order.krullDim C ≤ 0 := by
    rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    simp only [hall x, WithBot.coe_zero, le_refl]
  rw [hd] at hz
  norm_num at hz

/-- Final theorem: construct an actual compatible finite separable
parameter for the function field of a finite-type integral curve. All
field-generation and dimension hypotheses are derived from Scheme geometry.
Perfectness is imposed only on the ground field, and thus includes
algebraically closed fields of arbitrary characteristic. -/
theorem finiteType_curve_exists_separating_parameter
    (C : Scheme.{u}) [IsIntegral C] (hd : Order.krullDim C = 1)
    (k : Type u) [Field k] [PerfectField k]
    (b : C ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    [Algebra k C.functionField]
    (hbase : algebraMap k C.functionField = curveFunctionFieldBaseMap C k b) :
    ∃ f : RatFunc k →ₐ[k] C.functionField,
      letI : Algebra (RatFunc k) C.functionField := f.toRingHom.toAlgebra
      FiniteDimensional (RatFunc k) C.functionField ∧
        Algebra.IsSeparable (RatFunc k) C.functionField := by
  obtain ⟨x, hx⟩ := curve_exists_coheight_one C hd
  obtain ⟨hft, htr⟩ := curve_functionField_properties_of_closed_point C hd.le x hx k b hbase
  have := hft
  exact exists_compatible_finite_separable_ratFunc_embedding k C.functionField htr

end Negativity


