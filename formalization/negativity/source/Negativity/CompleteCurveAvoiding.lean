module

public import Negativity.CompleteCurveThroughPoint
public import Negativity.AffineCurveAvoiding
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: through a prescribed closed point of a proper
closed subset of an actual complete integral variety, construct a
complete integral curve not contained in that subset. Both meeting
and noncontainment are genuine geometric conclusions. -/
theorem exists_complete_integral_curve_through_closed_point_avoiding
    (X : Scheme.{u}) [IsIntegral X] (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsProper b]
    (S : Set X) (hS : IsClosed S) (hηS : genericPoint X ∉ S)
    (x : X) (hxc : IsClosed ({x} : Set X)) (hxS : x ∈ S) :
    ∃ (C : Scheme.{u}) (j : C ⟶ X), IsIntegral C ∧ Order.krullDim C = 1 ∧
      IsClosedImmersion j ∧ IsProper (j ≫ b) ∧ x ∈ Set.range j ∧ ¬ Set.range j ⊆ S := by
  classical
  have hx : x ≠ genericPoint X := fun h => hηS (h ▸ hxS)
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
  let T : Set (PrimeSpectrum R) := hU.fromSpec ⁻¹' S
  have hT : IsClosed T := hS.preimage hU.fromSpec.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal T).mp hT
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hxU⟩
  have hI0 : I ≠ ⊥ := by
    intro he
    have hTu : T = Set.univ := by rw [hI, he, PrimeSpectrum.zeroLocus_bot]
    have hmem : hU.primeIdealOf ⟨genericPoint X, hηU⟩ ∈ T := by rw [hTu]; trivial
    have hbad : hU.fromSpec (hU.primeIdealOf ⟨genericPoint X, hηU⟩) ∈ S := hmem
    rw [hU.fromSpec_primeIdealOf] at hbad
    exact hηS hbad
  have hmT : m ∈ T := by
    change hU.fromSpec m ∈ S
    rw [hU.fromSpec_primeIdealOf]
    exact hxS
  have hIm : I ≤ m.asIdeal := (PrimeSpectrum.mem_zeroLocus m I).mp (hI ▸ hmT)
  obtain ⟨v, hvI, hv⟩ := I.ne_bot_iff.mp hI0
  obtain ⟨P, hP, hPm, hvP, hdim, hnf⟩ := affine_integral_curve_through_maximal_avoiding k R
    (affine_chart_not_field_at_nonGeneric_point X x hx U hU hxU) m.asIdeal v hv (hIm hvI)
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
  obtain ⟨hInt, hdI, hproper, _⟩ := complete_integral_curve_actual_closure hdC k b f
  have hxq : m ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk P)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
    exact hPm.le
  obtain ⟨z, hz⟩ := hxq
  have hfx : f z = x := by
    change hU.fromSpec (q z) = x
    change hU.fromSpec (PrimeSpectrum.comap (Ideal.Quotient.mk P) z) = x
    rw [hz, hU.fromSpec_primeIdealOf]
  have hqη : (q (genericPoint C₀)).asIdeal = P := by
    change (PrimeSpectrum.comap (Ideal.Quotient.mk P) (genericPoint C₀)).asIdeal = P
    rw [genericPoint_eq_bot_of_affine]
    exact Ideal.mk_ker
  have hfη : f (genericPoint C₀) ∉ S := by
    intro hbad
    have hTη : q (genericPoint C₀) ∈ T := hbad
    have hIη : I ≤ (q (genericPoint C₀)).asIdeal :=
      (PrimeSpectrum.mem_zeroLocus (q (genericPoint C₀)) I).mp (hI ▸ hTη)
    exact hvP (hqη ▸ hIη hvI)
  refine ⟨f.image, f.imageι, hInt, hdI, inferInstance, hproper,
    ⟨f.toImage z, by simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using hfx⟩, ?_⟩
  intro hall
  apply hfη
  have hm := hall (Set.mem_range_self (f.toImage (genericPoint C₀)))
  simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using hm

end
end Negativity
