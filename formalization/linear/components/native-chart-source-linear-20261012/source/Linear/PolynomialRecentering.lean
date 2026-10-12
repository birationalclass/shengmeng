module
public import Linear.PolynomialFormalCompletion
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {σ K : Type*} [Field K]
attribute [local instance] polynomial_idealOfVars_isMaximal

theorem polynomialTranslation_evaluation (x y : σ → K) (P : MvPolynomial σ K) :
    MvPolynomial.eval y (polynomialTranslation x P) =
      MvPolynomial.eval (fun i => y i + x i) P := by
  have h : (MvPolynomial.aeval y).comp (polynomialTranslation x).toAlgHom =
      MvPolynomial.aeval (fun i => y i + x i) := by
    ext i
    simp [polynomialTranslation]
  exact congrArg (fun f => f P) h

theorem polynomialTranslation_origin_kernel (x : σ → K) :
    (MvPolynomial.idealOfVars σ K).comap (polynomialTranslation x).toRingHom =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
  rw [polynomial_idealOfVars_eq_constantCoeff_kernel]
  ext P
  change MvPolynomial.constantCoeff (polynomialTranslation x P) = 0 ↔
    MvPolynomial.aeval x P = 0
  simpa [MvPolynomial.eval_zero, MvPolynomial.aeval_def] using
    (congrArg (fun z => z = 0) (polynomialTranslation_evaluation x 0 P)).to_iff

theorem polynomialTranslation_primeCompl (x : σ → K) :
    letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
    (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).primeCompl.map
      (polynomialTranslation x).toRingEquiv = (MvPolynomial.idealOfVars σ K).primeCompl := by
  let : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  let P := RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom
  let e := (polynomialTranslation x).toRingEquiv
  have hKeq : (MvPolynomial.idealOfVars σ K).comap e = P := by
    change (MvPolynomial.idealOfVars σ K).comap (polynomialTranslation x).toRingHom =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom
    exact polynomialTranslation_origin_kernel x
  simpa only [hKeq] using e.map_primeCompl_comap_eq (MvPolynomial.idealOfVars σ K)

def polynomialPointLocalEquiv (x : σ → K) :
    letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
    Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) ≃+*
      Localization.AtPrime (MvPolynomial.idealOfVars σ K) := by
  let : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  exact IsLocalization.ringEquivOfRingEquiv _ _ (polynomialTranslation x).toRingEquiv
    (polynomialTranslation_primeCompl x)

theorem polynomialPointLocalEquiv_polynomial (x : σ → K) (P : MvPolynomial σ K) :
    letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
    polynomialPointLocalEquiv x
      (algebraMap (MvPolynomial σ K)
        (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)) P) =
      algebraMap (MvPolynomial σ K) (Localization.AtPrime (MvPolynomial.idealOfVars σ K))
        (polynomialTranslation x P) := by
  let : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  exact IsLocalization.ringEquivOfRingEquiv_eq (j := (polynomialTranslation x).toRingEquiv)
    (polynomialTranslation_primeCompl x) P

end LinearStudy
