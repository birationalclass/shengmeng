module
public import Linear.JacobianNonzero
public import Linear.TensorSpecialization
/-!
# The actual relative Jacobian survives the actual closed fiber

For characteristic-zero coefficients and the original finite flat regular
power-series equations, derive closed-fiber Jacobian nonvanishing, scalar
socle generation, and primitivity over the parameter base. No closed-fiber
regularity, finiteness, pairing, or Jacobian conclusion is an extra input.
Relative nilradical annihilation and arbitrary parameter lifts are separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped TensorProduct
namespace LinearStudy
variable {K : Type*} [Field K] [CharZero K] {r n : ℕ}
variable (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K))
variable (hH : RingTheory.Sequence.IsRegular
  (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K)) (List.ofFn H))
variable [Module.Finite (MvPowerSeries (Fin (r + 1)) K)
  (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))]
variable [Module.Flat (MvPowerSeries (Fin (r + 1)) K)
  (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸ Ideal.span (Set.range H))]
include hH

theorem finiteFlat_closedFiber_jacobian_nonzero :
    powerSeriesJacobianClass (fun i => parameterSpecialization (H i)) ≠ 0 := by
  let := powerSeries_specialized_quotient_finite H
  let := powerSeries_specialized_quotient_artinian H
  exact powerSeriesQuotient_jacobian_nonzero _
    (powerSeries_specialized_equations_regular H hH)
    (powerSeries_specialized_equations_zeroConstant H hH)

theorem finiteFlat_residueTensor_jacobian_nonzero :
    (1 ⊗ₜ[MvPowerSeries (Fin (r + 1)) K]
      Ideal.Quotient.mk (Ideal.span (Set.range H))
        (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) :
        (MvPowerSeries (Fin (r + 1)) K ⧸
          IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K)) ⊗[MvPowerSeries (Fin (r + 1)) K]
          (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸
            Ideal.span (Set.range H))) ≠ 0 := by
  intro hz
  have he := congrArg (powerSeriesResidueTensorEquiv H) hz
  rw [powerSeriesResidueTensorEquiv_one_tmul, map_zero,
    parameterSpecialization_jacobian] at he
  exact finiteFlat_closedFiber_jacobian_nonzero H hH he

theorem finiteFlat_jacobian_primitive :
    Ideal.Quotient.mk (Ideal.span (Set.range H))
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) ∉
        IsLocalRing.maximalIdeal (MvPowerSeries (Fin (r + 1)) K) •
          (⊤ : Submodule (MvPowerSeries (Fin (r + 1)) K)
            (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) K) ⧸
              Ideal.span (Set.range H))) := by
  exact primitive_of_residue_tensor_nonzero _
    (finiteFlat_residueTensor_jacobian_nonzero H hH)

theorem finiteFlat_residueTensor_jacobian_scalar_socle :
    let B := MvPowerSeries (Fin (r + 1)) K
    let A := MvPowerSeries (Fin (n + 1)) B ⧸ Ideal.span (Set.range H)
    let k := B ⧸ IsLocalRing.maximalIdeal B
    let C := k ⊗[B] A
    ∀ x : C, Annihilates (nilradical C) x →
      ∃ u : k, x = u • (1 ⊗ₜ[B] Ideal.Quotient.mk (Ideal.span (Set.range H))
        (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i)))) := by
  let B := MvPowerSeries (Fin (r + 1)) K
  let A := MvPowerSeries (Fin (n + 1)) B ⧸ Ideal.span (Set.range H)
  let k := B ⧸ IsLocalRing.maximalIdeal B
  let : Field k := Ideal.Quotient.field _
  let C := k ⊗[B] A
  let Hbar := fun i => parameterSpecialization (H i)
  let Q := MvPowerSeries (Fin (n + 1)) K ⧸ Ideal.span (Set.range Hbar)
  let e : C ≃+* Q := powerSeriesResidueTensorEquiv H
  have hzero := powerSeries_specialized_equations_zeroConstant H hH
  let a := powerSeriesQuotientAugmentation Hbar hzero
  let : Nontrivial Q := a.toRingHom.domain_nontrivial
  let : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Ideal.span (Set.range Hbar))) Ideal.Quotient.mk_surjective
  let := powerSeries_specialized_quotient_finite H
  let := powerSeries_specialized_quotient_artinian H
  have hm : nilradical Q = IsLocalRing.maximalIdeal Q := by
    rw [← powerSeriesQuotientAugmentation_kernel_nilradical Hbar hzero]
    exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective a.toRingHom
      (powerSeriesQuotientAugmentation_surjective Hbar hzero))
  have hsocQ : ∀ x : Q, x ∈ (IsLocalRing.maximalIdeal Q).annihilator →
      ∃ b : K, x = b • powerSeriesJacobianClass Hbar := by
    intro x hx
    apply (powerSeriesQuotient_jacobian_scalar_socle Hbar
      (powerSeries_specialized_equations_regular H hH) hzero x).mp
    apply (annihilates_iff_mem_annihilator _ _).mpr
    rwa [hm]
  have he : e (1 ⊗ₜ[B] Ideal.Quotient.mk (Ideal.span (Set.range H))
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i)))) =
      powerSeriesJacobianClass Hbar := by
    rw [powerSeriesResidueTensorEquiv_one_tmul, parameterSpecialization_jacobian]
    rfl
  change ∀ x : C, Annihilates (nilradical C) x →
    ∃ u : k, x = u • (1 ⊗ₜ[B] Ideal.Quotient.mk (Ideal.span (Set.range H))
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))))
  intro x hx
  have hqx : Annihilates (nilradical Q) (e x) := by
    intro z hz
    have hz' : e.symm z ∈ nilradical C := by
      obtain ⟨j, hj⟩ := mem_nilradical.mp hz
      apply mem_nilradical.mpr
      refine ⟨j, e.injective ?_⟩
      rw [map_pow, e.apply_symm_apply, map_zero]
      exact hj
    have ht := congrArg e (hx (e.symm z) hz')
    simpa only [map_mul, e.apply_symm_apply, map_zero] using ht
  obtain ⟨u, hu⟩ := (powerSeriesQuotient_jacobian_scalar_socle Hbar
    (powerSeries_specialized_equations_regular H hH) hzero (e x)).mp hqx
  refine ⟨powerSeriesResidueFieldEquiv.symm u, e.injective ?_⟩
  rw [powerSeriesResidueTensorEquiv_smul, RingEquiv.apply_symm_apply, he]
  exact hu
end LinearStudy
