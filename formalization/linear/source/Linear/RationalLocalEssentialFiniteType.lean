module
public import Linear.LocalPullbackEssentialFiniteType
public import Linear.ProjectiveRationalChart
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- The actual rational polynomial chart's local quotient pullback is
essentially of finite type without a separate finiteness input. -/
theorem rationalPointLocalQuotientPullback_essFiniteType
    {K σ : Type*} [Field K] [Finite σ]
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K)
    (I J : Ideal (MvPolynomial σ K))
    (P : Ideal (Localization.Away p0)) (Q : Ideal (MvPolynomial σ K))
    [P.IsPrime] [Q.IsPrime]
    (hQP : Q = P.comap (rationalPolynomialChartMap p0 p).toRingHom)
    (hφ : I.map (rationalPolynomialChartMap p0 p).toRingHom ≤
      J.map (algebraMap (MvPolynomial σ K) (Localization.Away p0))) :
    letI := (generalPointLocalQuotientPullback I
      (J.map (algebraMap (MvPolynomial σ K) (Localization.Away p0))) P Q
      (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).toAlgebra
    Algebra.EssFiniteType
      (Localization.AtPrime Q ⧸ I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime Q)))
      (Localization.AtPrime P ⧸
        (J.map (algebraMap (MvPolynomial σ K) (Localization.Away p0))).map
          (algebraMap (Localization.Away p0) (Localization.AtPrime P))) := by
  change (generalPointLocalQuotientPullback I
    (J.map (algebraMap (MvPolynomial σ K) (Localization.Away p0))) P Q
    (rationalPolynomialChartMap p0 p).toRingHom hQP hφ).EssFiniteType
  exact generalPointLocalQuotientPullback_essFiniteType I _ P Q
    (rationalPolynomialChartMap p0 p) hQP hφ

end LinearStudy
