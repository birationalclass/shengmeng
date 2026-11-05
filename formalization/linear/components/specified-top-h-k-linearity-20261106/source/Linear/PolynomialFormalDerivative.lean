module
public import Linear.PolynomialFormalFiber
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPowerSeries.Derivative
/-! Actual point translation, derivative evaluation and canonical transfer of
point-local polynomial ideal generators into the completed formal ring. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K]

theorem polynomialTranslation_pderiv (x : σ → K) (P : MvPolynomial σ K) (j : σ) :
    MvPolynomial.pderiv j (polynomialTranslation x P) =
      polynomialTranslation x (MvPolynomial.pderiv j P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [polynomialTranslation]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, polynomialTranslation_X, Derivation.leibniz, map_add,
      MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, hP, MvPolynomial.pderiv_C]
    split_ifs <;> simp

theorem formalPolynomialAtPoint_constantCoeff (x : σ → K) (P : MvPolynomial σ K) :
    (formalPolynomialAtPoint x P).constantCoeff = MvPolynomial.eval x P := by
  change MvPowerSeries.constantCoeff ((polynomialTranslation x P : MvPolynomial σ K) :
    MvPowerSeries σ K) = _
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
  have h := polynomialTranslation_evaluation x 0 P
  simpa only [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, Pi.zero_apply,
    zero_add] using h

theorem formalPolynomialAtPoint_pderiv (x : σ → K) (P : MvPolynomial σ K) (j : σ) :
    MvPowerSeries.pderiv j (formalPolynomialAtPoint x P) =
      formalPolynomialAtPoint x (MvPolynomial.pderiv j P) := by
  change MvPowerSeries.pderiv j ((polynomialTranslation x P : MvPolynomial σ K) :
    MvPowerSeries σ K) = _
  rw [MvPowerSeries.pderiv_coe, polynomialTranslation_pderiv]
  rfl

theorem formalPolynomialAtPoint_jacobian_at_point (x : σ → K)
    (P : σ → MvPolynomial σ K) (i j : σ) :
    (MvPowerSeries.pderiv j (formalPolynomialAtPoint x (P i))).constantCoeff =
      MvPolynomial.eval x (MvPolynomial.pderiv j (P i)) := by
  rw [formalPolynomialAtPoint_pderiv, formalPolynomialAtPoint_constantCoeff]

@[simp] theorem formalPolynomialAtPoint_C (x : σ → K) (a : K) :
    formalPolynomialAtPoint x (MvPolynomial.C a) = MvPowerSeries.C a := by
  simp [formalPolynomialAtPoint, polynomialTranslation]

theorem formalPolynomialAtPoint_X (x : σ → K) (i : σ) :
    formalPolynomialAtPoint x (MvPolynomial.X i) = MvPowerSeries.X i + MvPowerSeries.C (x i) := by
  simp [formalPolynomialAtPoint, polynomialTranslation, MvPolynomial.coe_X, MvPolynomial.coe_C]

theorem formalPolynomialAtPoint_centered_X (x : σ → K) (i : σ) :
    formalPolynomialAtPoint x (MvPolynomial.X i - MvPolynomial.C (x i)) = MvPowerSeries.X i := by
  rw [map_sub, formalPolynomialAtPoint_X, formalPolynomialAtPoint_C, add_sub_cancel_right]

theorem formalPolynomialIdeal_local_generators [Finite σ]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    {ι : Type*} (G : ι → MvPolynomial σ K)
    (hlocal : I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap (MvPolynomial σ K) (Localization.AtPrime P) (G i)))) :
    I.map (formalPolynomialAtPoint x) = Ideal.span (Set.range (fun i => formalPolynomialAtPoint x (G i))) := by
  let S := Localization.AtPrime P
  let T := AdicCompletion (IsLocalRing.maximalIdeal S) S
  let E := polynomialPrimeFormalCompletionEquiv P x hP
  let χ : S →+* MvPowerSeries σ K := E.symm.toRingHom.comp (algebraMap S T)
  have hχ : χ.comp (algebraMap (MvPolynomial σ K) S) = formalPolynomialAtPoint x := by
    apply RingHom.ext
    intro F
    apply E.injective
    change E (E.symm (algebraMap S T (algebraMap (MvPolynomial σ K) S F))) = E (formalPolynomialAtPoint x F)
    rw [E.apply_symm_apply]
    exact (polynomialPrimeFormalCompletionEquiv_polynomial P x hP F).symm
  have h := congrArg (fun J : Ideal S => J.map χ) hlocal
  rw [Ideal.map_map, hχ, Ideal.map_span, ← Set.range_comp] at h
  have hval (F : MvPolynomial σ K) : χ (algebraMap (MvPolynomial σ K) S F) = formalPolynomialAtPoint x F :=
    DFunLike.congr_fun hχ F
  change I.map (formalPolynomialAtPoint x) =
    Ideal.span (Set.range (fun i => χ (algebraMap (MvPolynomial σ K) S (G i)))) at h
  have hfun : (fun i => χ (algebraMap (MvPolynomial σ K) S (G i))) =
      (fun i => formalPolynomialAtPoint x (G i)) := funext (fun i => hval (G i))
  rw [hfun] at h
  exact h

end LinearStudy
