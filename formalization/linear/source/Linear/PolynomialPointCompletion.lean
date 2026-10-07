module
public import Linear.PolynomialRecentering
public import Linear.CompletionCongr
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {σ K : Type*} [Field K] [Finite σ]
attribute [local instance] polynomial_idealOfVars_isMaximal

/-- The formal coordinates at an actual arbitrary rational affine point. -/
def polynomialPointFormalCompletionEquiv (x : σ → K) :
    letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
    MvPowerSeries σ K ≃+* AdicCompletion
      (IsLocalRing.maximalIdeal
        (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)))
      (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)) := by
  let : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  exact (polynomialOriginFormalCompletionEquiv σ K).trans
    (completionCongrRingEquiv (polynomialPointLocalEquiv x) _ _
      (IsLocalRing.map_ringEquiv_maximalIdeal (polynomialPointLocalEquiv x)).symm).symm

theorem polynomialPointFormalCompletionEquiv_polynomial (x : σ → K)
    (P : MvPolynomial σ K) :
    letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
    polynomialPointFormalCompletionEquiv x (polynomialTranslation x P) =
      AdicCompletion.of
        (IsLocalRing.maximalIdeal
          (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)))
        (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom))
        (algebraMap (MvPolynomial σ K)
          (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)) P) := by
  let : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  change (completionCongrRingEquiv (polynomialPointLocalEquiv x) _ _
      (IsLocalRing.map_ringEquiv_maximalIdeal (polynomialPointLocalEquiv x)).symm).symm
    (polynomialOriginFormalCompletionEquiv σ K (polynomialTranslation x P)) = _
  apply (completionCongrRingEquiv (polynomialPointLocalEquiv x) _ _
      (IsLocalRing.map_ringEquiv_maximalIdeal (polynomialPointLocalEquiv x)).symm).injective
  rw [RingEquiv.apply_symm_apply, polynomialOriginFormalCompletionEquiv_polynomial,
    completionCongrRingEquiv_of, polynomialPointLocalEquiv_polynomial]

end LinearStudy
