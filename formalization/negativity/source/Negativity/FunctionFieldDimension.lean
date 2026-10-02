module

public import Negativity.AffineCurveThroughPoint
public import Negativity.CurveFunctionField
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem finiteType_domain_dimension_of_trdeg_le_one
    (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] (hd : Algebra.trdeg k R ≤ 1) :
    Ring.KrullDimLE 1 R := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k R
  let B := MvPolynomial (Fin n) k
  let : Algebra B R := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral B R := ⟨hint⟩
  have : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).mpr hg
  have : IsScalarTower k B R := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have heq := trdeg_add_eq k B (A := R)
  rw [trdeg_eq_zero (R := B) (A := R), add_zero] at heq
  have hn : n ≤ 1 := by
    rw [← heq] at hd
    change Algebra.trdeg k (MvPolynomial (Fin n) k) ≤ 1 at hd
    rw [MvPolynomial.trdeg_of_isDomain] at hd
    simpa using hd
  have : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_iff]
    change ringKrullDim (MvPolynomial (Fin n) k) ≤ 1
    simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    exact_mod_cast hn
  exact integral_extension_krullDimLE_one B R

theorem affine_chart_dimension_of_functionField_trdeg_le_one
    (X : Scheme.{u}) [IsIntegral X] (k : Type u) [Field k]
    (b : X ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    [Algebra k X.functionField]
    (hbase : algebraMap k X.functionField = curveFunctionFieldBaseMap X k b)
    (hd : Algebra.trdeg k X.functionField ≤ 1)
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Ring.KrullDimLE 1 Γ(X, U) := by
  let R := Γ(X, U)
  let c : k →+* R := (Spec.preimage (hU.fromSpec ≫ b)).hom
  let : Algebra k R := c.toAlgebra
  have hc : c.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.FiniteType k R := hc
  have : IsFractionRing R X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsScalarTower k R X.functionField := IsScalarTower.of_algebraMap_eq' (by
    rw [hbase]
    exact (curve_affine_constants_compatible X U hU k b).symm)
  have : Algebra.IsAlgebraic R X.functionField :=
    IsLocalization.isAlgebraic X.functionField (nonZeroDivisors R)
  have : FaithfulSMul R X.functionField :=
    (faithfulSMul_iff_algebraMap_injective R X.functionField).mpr (IsFractionRing.injective _ _)
  have heq := trdeg_add_eq k R (A := X.functionField)
  rw [trdeg_eq_zero (R := R) (A := X.functionField), add_zero] at heq
  apply finiteType_domain_dimension_of_trdeg_le_one k R
  exact heq ▸ hd

/-- Final theorem: the dimension bound for an actual finite-type integral
scheme follows from the transcendence degree of its actual generic field.
This applies to the closure of an affine curve, including its boundary. -/
theorem integral_scheme_dimension_of_functionField_trdeg_le_one
    (X : Scheme.{u}) [IsIntegral X] (k : Type u) [Field k]
    (b : X ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    [Algebra k X.functionField]
    (hbase : algebraMap k X.functionField = curveFunctionFieldBaseMap X k b)
    (hd : Algebra.trdeg k X.functionField ≤ 1) : Order.krullDim X ≤ 1 := by
  rw [Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have := affine_chart_dimension_of_functionField_trdeg_le_one X k b hbase hd U hU
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hp := Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
  have hr := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 Γ(X, U))
  have hle := hp.trans hr
  rw [idealHeight_eq_coheight] at hle
  change (Order.coheight (hU.isoSpec.hom ⟨x, hxU⟩) : WithBot ℕ∞) ≤ 1 at hle
  rw [coheight_eq_of_isOpenImmersion] at hle
  have he := coheight_eq_of_isOpenImmersion (x := (⟨x, hxU⟩ : U.toScheme)) U.ι
  rw [← he] at hle
  exact hle

end Negativity
