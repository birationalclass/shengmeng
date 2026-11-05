module
public import Linear.FiniteSpecialization
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Linear.ResiduePairing
public import Linear.SocleTransport

/-!
# Actual residue tensor comparison and relative perfect pairing

Identify the residue-field tensor product with the specialized power-series
equation quotient, including the element and residue-scalar formulas.
Transfer the proved scalar socle through this actual ring equivalence, then
lift its perfect multiplication pairing to the original finite flat algebra.
No socle, closed-fiber finiteness or relative pairing hypothesis is used in
the final construction. The derivative Jacobian comparison is still open.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
open scoped TensorProduct
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ}

theorem powerSeries_maximalIdeal_eq_coordinates :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K) =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin (r + 1)) (R := K))) := by
  rw [← powerSeries_constantCoeff_kernel]
  ext b
  change ¬ IsUnit b ↔ b.constantCoeff = 0
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

theorem parameterIdeal_map_eq_residueIdeal
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K)) :
    (Ideal.span (Set.range (fun i : Fin (r + 1) =>
      MvPowerSeries.C (σ := Fin c) (MvPowerSeries.X (R := K) i)))).map
        (Ideal.Quotient.mk (Ideal.span (Set.range H))) =
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)).map
        (algebraMap (MvPowerSeries (Fin (r + 1)) K)
          (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))) := by
  rw [powerSeries_maximalIdeal_eq_coordinates, Ideal.map_span, Ideal.map_span,
    ← Set.range_comp, ← Set.range_comp]
  congr 1

def powerSeriesResidueTensorEquiv
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K)) :
    ((MvPowerSeries (Fin (r + 1)) K ⧸
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)) ⊗[MvPowerSeries (Fin (r + 1)) K]
        (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))) ≃+*
      (MvPowerSeries (Fin c) K ⧸
        Ideal.span (Set.range (fun i => parameterSpecialization (H i)))) := by
  let A := MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H)
  let m := IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A m).symm.toRingEquiv.trans
    ((Ideal.quotEquivOfEq (parameterIdeal_map_eq_residueIdeal H).symm).trans
      (powerSeriesClosedQuotientEquiv H))

theorem powerSeriesResidueTensorEquiv_one_tmul
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
    (z : MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K)) :
    powerSeriesResidueTensorEquiv H (1 ⊗ₜ[MvPowerSeries (Fin (r + 1)) K]
      Ideal.Quotient.mk (Ideal.span (Set.range H)) z) =
      Ideal.Quotient.mk _ (parameterSpecialization z) := by
  let A := MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H)
  let m := IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A m
  have ht : e.symm (1 ⊗ₜ[MvPowerSeries (Fin (r + 1)) K]
      Ideal.Quotient.mk (Ideal.span (Set.range H)) z) =
      Ideal.Quotient.mk (m.map (algebraMap (MvPowerSeries (Fin (r + 1)) K) A))
        (Ideal.Quotient.mk (Ideal.span (Set.range H)) z) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk A m _).symm
  dsimp only [powerSeriesResidueTensorEquiv, RingEquiv.trans_apply]
  change powerSeriesClosedQuotientEquiv H
    ((Ideal.quotEquivOfEq (parameterIdeal_map_eq_residueIdeal H).symm)
      (e.symm (1 ⊗ₜ[MvPowerSeries (Fin (r + 1)) K]
        Ideal.Quotient.mk (Ideal.span (Set.range H)) z))) = _
  rw [ht]
  exact powerSeriesClosedQuotientEquiv_mk H z

def powerSeriesResidueFieldEquiv :
    (MvPowerSeries (Fin (r + 1)) K ⧸
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)) ≃+* K :=
  (Ideal.quotEquivOfEq (powerSeries_maximalIdeal_eq_coordinates.trans
    powerSeries_constantCoeff_kernel.symm)).trans
      (RingHom.quotientKerEquivOfSurjective
        (f := MvPowerSeries.constantCoeff (σ := Fin (r + 1)) (R := K))
        (fun k => ⟨MvPowerSeries.C k, by simp⟩))

theorem powerSeriesResidueFieldEquiv_mk (b : MvPowerSeries (Fin (r + 1)) K) :
    powerSeriesResidueFieldEquiv (Ideal.Quotient.mk _ b) = b.constantCoeff := rfl

theorem powerSeriesResidueTensorEquiv_algebraMap
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
    (u : MvPowerSeries (Fin (r + 1)) K ⧸
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)) :
    powerSeriesResidueTensorEquiv H
      (u ⊗ₜ[MvPowerSeries (Fin (r + 1)) K]
        (1 : MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))) =
      algebraMap K (MvPowerSeries (Fin c) K ⧸
        Ideal.span (Set.range (fun i => parameterSpecialization (H i))))
          (powerSeriesResidueFieldEquiv u) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [powerSeriesResidueFieldEquiv_mk]
  change powerSeriesResidueTensorEquiv H
    (algebraMap (MvPowerSeries (Fin (r + 1)) K) _ b ⊗ₜ[MvPowerSeries (Fin (r + 1)) K] 1) = _
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  change powerSeriesResidueTensorEquiv H
    (1 ⊗ₜ[MvPowerSeries (Fin (r + 1)) K]
      Ideal.Quotient.mk (Ideal.span (Set.range H)) (MvPowerSeries.C b)) = _
  rw [powerSeriesResidueTensorEquiv_one_tmul]
  simp only [parameterSpecialization, MvPowerSeries.map_C]
  change Ideal.Quotient.mk _ (MvPowerSeries.C b.constantCoeff) =
    Ideal.Quotient.mk _ (algebraMap K (MvPowerSeries (Fin c) K) b.constantCoeff)
  rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self]
  rfl

theorem powerSeriesResidueTensorEquiv_smul
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
    (u : MvPowerSeries (Fin (r + 1)) K ⧸
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K))
    (a : (MvPowerSeries (Fin (r + 1)) K ⧸
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)) ⊗[MvPowerSeries (Fin (r + 1)) K]
        (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))) :
    powerSeriesResidueTensorEquiv H (u • a) =
      powerSeriesResidueFieldEquiv u • powerSeriesResidueTensorEquiv H a := by
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.smul_tmul']
    change powerSeriesResidueTensorEquiv H ((u * x) ⊗ₜ[MvPowerSeries (Fin (r + 1)) K] y) = _
    have hprod : (u * x) ⊗ₜ[MvPowerSeries (Fin (r + 1)) K] y =
        (u ⊗ₜ[MvPowerSeries (Fin (r + 1)) K] 1) *
          (x ⊗ₜ[MvPowerSeries (Fin (r + 1)) K] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hprod, map_mul, powerSeriesResidueTensorEquiv_algebraMap]
    exact (Algebra.smul_def (R := K)
      (A := MvPowerSeries (Fin c) K ⧸
        Ideal.span (Set.range (fun i => parameterSpecialization (H i))))
      (powerSeriesResidueFieldEquiv u) _).symm
  | add a b ha hb => simp only [smul_add, map_add, ha, hb]

theorem finiteFlat_powerSeries_relative_perfectPairing
    {K : Type*} [Field K] {r n : ℕ}
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K))
    (hH : RingTheory.Sequence.IsRegular
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K)) (List.ofFn H))
    [Module.Finite (MvPowerSeries (Fin (r + 1)) K)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))]
    [Module.Flat (MvPowerSeries (Fin (r + 1)) K)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))] :
    Nonempty (PerfectMultiplicationPairing (B := MvPowerSeries (Fin (r + 1)) K)
      (A := MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))) := by
  let B := MvPowerSeries (Fin (r + 1)) K
  let A := MvPowerSeries (Fin (n + 1)) B ⧸ Ideal.span (Set.range H)
  let k := B ⧸ IsLocalRing.maximalIdeal B
  let C := k ⊗[B] A
  let Hbar := fun i => parameterSpecialization (H i)
  let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range Hbar)
  let e : C ≃+* Q := powerSeriesResidueTensorEquiv H
  have hreg := powerSeries_specialized_equations_regular H hH
  have hzero := powerSeries_specialized_equations_zeroConstant H hH
  have hproper : Ideal.span (Set.range Hbar) ≠ ⊤ := by
    intro ht
    apply hreg.top_ne_smul
    rw [ideal_ofFn, ht, Submodule.top_smul]
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span (Set.range Hbar))) Ideal.Quotient.mk_surjective
  let : Nontrivial C := e.toEquiv.nontrivial
  let : IsLocalRing C := IsLocalRing.of_surjective' (R := Q) (S := C)
    e.symm.toRingHom (fun a => by obtain ⟨b, hb⟩ := e.symm.surjective a; exact ⟨b, hb⟩)
  let : Field k := Ideal.Quotient.field _
  let := powerSeries_specialized_quotient_artinian H
  obtain ⟨M, hM, hd, hsoc⟩ := powerSeries_coefficientDeterminant_scalar_socle Hbar hreg hzero
  let delta : Q := Ideal.Quotient.mk (Ideal.span (Set.range Hbar)) M.det
  have hsocQ : ∀ a : Q, a ∈ (IsLocalRing.maximalIdeal Q).annihilator →
      ∃ u : K, a = u • delta := by
    intro a ha
    apply hsoc a
    rwa [IsLocalRing.eq_maximalIdeal (powerSeries_quotient_coordinateIdeal_isMaximal Hbar hzero)]
  have hdC : e.symm delta ≠ 0 := by
    intro h
    apply hd
    have hh := congrArg e h
    simpa only [e.apply_symm_apply, map_zero] using hh
  apply exists_finiteFlat_pairing_of_residue_socle (B := B) (A := A) (e.symm delta) hdC
  apply scalar_socle_transport (C := C) (D := Q) (k := k) (K := K) e
    (powerSeriesResidueFieldEquiv (K := K) (r := r)) _ delta hsocQ
  intro u a
  exact powerSeriesResidueTensorEquiv_smul H u a

end LinearStudy
