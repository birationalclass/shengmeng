module
public import Linear.PolynomialPointCompletion
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

def polynomialPointLocalEvaluation {K σ : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) :
    Localization.AtPrime P →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := P.primeCompl) (S := Localization.AtPrime P)
    (f := MvPolynomial.aeval (R := K) x) (fun y => by
    apply isUnit_iff_ne_zero.mpr
    intro hy
    apply y.property
    have hm : (y : MvPolynomial σ K) ∈ RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := hy
    exact hP.symm ▸ hm)

theorem polynomialPointLocalEvaluation_polynomial {K σ : Type*} [Field K]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime] (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : MvPolynomial σ K) :
    polynomialPointLocalEvaluation P x hP
      (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) G) = MvPolynomial.eval x G := by
  unfold polynomialPointLocalEvaluation
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

theorem polynomialPointLocalEvaluation_kills_ideal {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) :
    I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P)) ≤
      RingHom.ker (polynomialPointLocalEvaluation P x hP).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro G hG
  change polynomialPointLocalEvaluation P x hP
    (algebraMap (MvPolynomial σ K) (Localization.AtPrime P) G) = 0
  rw [polynomialPointLocalEvaluation_polynomial]
  have hp := hIP hG
  rw [hP, RingHom.mem_ker] at hp
  exact hp

def polynomialPointLocalQuotientEvaluation {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom) :
    (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (polynomialPointLocalEvaluation P x hP)
    (fun _ ha => polynomialPointLocalEvaluation_kills_ideal I P hIP x hP ha)

theorem polynomialPointLocalQuotientEvaluation_polynomial {K σ : Type*} [Field K]
    (I P : Ideal (MvPolynomial σ K)) [P.IsPrime] (hIP : I ≤ P) (x : σ → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : MvPolynomial σ K) :
    polynomialPointLocalQuotientEvaluation I P hIP x hP
      (Ideal.Quotient.mk (I.map (algebraMap _ (Localization.AtPrime P)))
        (algebraMap _ (Localization.AtPrime P) G)) = MvPolynomial.eval x G := by
  exact polynomialPointLocalEvaluation_polynomial P x hP G

end LinearStudy
