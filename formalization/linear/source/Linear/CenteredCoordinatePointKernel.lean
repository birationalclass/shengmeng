module
public import Linear.RationalTargetCenterUnramified
public import Linear.LocalGeneratorsEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

/-- Reindexing, inverse linear coordinates and centering take the SAME
actual target point prime to the origin prime; this is not a prime input. -/
theorem centered_target_coordinate_point_kernel
    {K σ τ : Type*} [Field K] [Fintype τ] [DecidableEq τ]
    (b : σ ≃ τ) (M : Matrix τ τ K) (hM : Matrix.det M ≠ 0) (y : σ → K) :
    let E0 := MvPolynomial.renameEquiv K b
    let EL := polynomialLinearChangeEquiv M hM
    let z := M⁻¹ *ᵥ (y ∘ b.symm)
    let EC := polynomialTranslation z
    (((RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom).comap E0.symm.toRingHom).comap
      EL.symm.toRingHom).comap EC.symm.toRingHom =
        RingHom.ker (MvPolynomial.aeval (R := K) (0 : τ → K)).toRingHom := by
  intro E0 EL z EC
  have h0 : (RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom).comap E0.symm.toRingHom =
      RingHom.ker (MvPolynomial.aeval (R := K) (y ∘ b.symm)).toRingHom := by
    ext F
    change MvPolynomial.eval y (MvPolynomial.rename b.symm F) = 0 ↔
      MvPolynomial.eval (y ∘ b.symm) F = 0
    rw [MvPolynomial.eval_rename]
  have hL : ((RingHom.ker (MvPolynomial.aeval (R := K) y).toRingHom).comap E0.symm.toRingHom).comap
      EL.symm.toRingHom = RingHom.ker (MvPolynomial.aeval (R := K) z).toRingHom := by
    rw [h0]
    ext F
    change MvPolynomial.eval (y ∘ b.symm) (polynomialLinearChange M⁻¹ F) = 0 ↔
      MvPolynomial.eval z F = 0
    rw [eval_polynomialLinearChange]
  rw [hL]
  have hC : RingHom.ker (MvPolynomial.aeval (R := K) z).toRingHom =
      (RingHom.ker (MvPolynomial.aeval (R := K) (0 : τ → K)).toRingHom).comap EC.toRingHom := by
    ext F
    change MvPolynomial.eval z F = 0 ↔ MvPolynomial.eval (0 : τ → K) (EC F) = 0
    simp only [EC, polynomialTranslation_evaluation, Pi.zero_apply, zero_add]
  rw [hC, Ideal.comap_comap]
  ext F
  change MvPolynomial.eval (0 : τ → K) (EC (EC.symm F)) = 0 ↔
    MvPolynomial.eval (0 : τ → K) F = 0
  rw [EC.apply_symm_apply]

end LinearStudy
