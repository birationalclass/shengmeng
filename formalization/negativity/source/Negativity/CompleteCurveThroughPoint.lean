module

public import Negativity.CompleteCurveClosure
public import Negativity.CurveImageCases
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem affine_chart_not_field_at_nonGeneric_point
    (X : Scheme.{u}) [IsIntegral X] (x : X) (hx : x ≠ genericPoint X)
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U) :
    ¬ IsField Γ(X, U) := by
  intro h
  let := h.toField
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hxU⟩
  have he : hU.primeIdealOf ⟨x, hxU⟩ = hU.primeIdealOf ⟨genericPoint X, hηU⟩ :=
    Subsingleton.elim _ _
  have he' := congrArg hU.fromSpec he
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at he'
  exact hx he'

theorem dimension_one_of_curve_domain
    (R : Type*) [CommRing R] [IsDomain R] [Ring.KrullDimLE 1 R]
    (hR : ¬ IsField R) : ringKrullDim R = 1 := by
  apply eq_of_le_of_not_lt (Ring.krullDimLE_iff.mp inferInstance)
  intro hlt
  have hz : ringKrullDim R ≤ 0 := Order.le_of_lt_succ hlt
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hz
  exact hR Ring.KrullDimLE.isField_of_isDomain

/-- Final theorem: in an actual complete integral variety over an
algebraically closed field, every closed nongeneric point lies on an
actual closed complete integral curve. Neither an affine curve, its
closure, its one-dimensionality nor a curve-existence predicate is input. -/
theorem exists_complete_integral_curve_through_closed_point
    (X : Scheme.{u}) [IsIntegral X] (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsProper b]
    (x : X) (hxc : IsClosed ({x} : Set X)) (hx : x ≠ genericPoint X) :
    ∃ (C : Scheme.{u}) (j : C ⟶ X), IsIntegral C ∧ Order.krullDim C = 1 ∧
      IsClosedImmersion j ∧ IsProper (j ≫ b) ∧ x ∈ Set.range j := by
  classical
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let R := Γ(X, U)
  let c : k →+* R := (Spec.preimage (hU.fromSpec ≫ b)).hom
  let : Algebra k R := c.toAlgebra
  have hc : c.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  have : Algebra.FiniteType k R := hc
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let m := hU.primeIdealOf ⟨x, hxU⟩
  have : m.asIdeal.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hxc
  obtain ⟨P, hP, hPm, hdim, hnf⟩ := affine_integral_curve_through_maximal k R
    (affine_chart_not_field_at_nonGeneric_point X x hx U hU hxU) m.asIdeal
  have := hP
  have := hdim
  let C₀ := Spec (.of (R ⧸ P))
  let q : C₀ ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))
  let f : C₀ ⟶ X := q ≫ hU.fromSpec
  have : QuasiCompact f := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hdC : Order.krullDim C₀ = 1 := by
    rw [Order.krullDim_eq_of_orderIso (specOrderIsoPrimeSpectrum (.of (R ⧸ P))),
      Order.krullDim_orderDual]
    exact dimension_one_of_curve_domain (R ⧸ P) hnf
  obtain ⟨hI, hdI, hproper, _⟩ := complete_integral_curve_actual_closure hdC k b f
  have hxq : m ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk P)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
    exact hPm.le
  obtain ⟨z, hz⟩ := hxq
  have hfx : f z = x := by
    change hU.fromSpec (q z) = x
    change hU.fromSpec (PrimeSpectrum.comap (Ideal.Quotient.mk P) z) = x
    rw [hz, hU.fromSpec_primeIdealOf]
  exact ⟨f.image, f.imageι, hI, hdI, inferInstance, hproper,
    ⟨f.toImage z, by simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using hfx⟩⟩

end
end Negativity
