module
public import Linear.LocalFiber
public import Linear.ProjectiveRationalChart
public import Mathlib.RingTheory.Localization.Ideal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Quotienting the polynomial denominator open gives the actual variety denominator open. -/
def awayQuotientEquiv
    {R : Type*} [CommRing R] (I : Ideal R) (a : R) :
    (Localization.Away a ⧸ I.map (algebraMap R (Localization.Away a))) ≃ₐ[R ⧸ I]
      Localization.Away (Ideal.Quotient.mk I a) := by
  let C := Localization.Away a ⧸ I.map (algebraMap R (Localization.Away a))
  have he : Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers a) =
      Submonoid.powers (Ideal.Quotient.mk I a) := by
    exact Submonoid.map_powers (Ideal.Quotient.mk I) a
  letI : IsLocalization (Submonoid.powers (Ideal.Quotient.mk I a)) C := he ▸
    (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers a)) C)
  exact IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I a)) C
    (Localization.Away (Ideal.Quotient.mk I a))

theorem awayQuotientEquiv_mk
    {R : Type*} [CommRing R] (I : Ideal R) (a r : R) :
    awayQuotientEquiv I a (Ideal.Quotient.mk _ (algebraMap R (Localization.Away a) r)) =
      algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I a)) (Ideal.Quotient.mk I r) :=
  (awayQuotientEquiv I a).commutes (Ideal.Quotient.mk I r)

/-- The same canonical quotient/open equivalence, over the original base ring. -/
def awayQuotientBaseEquiv
    {K R : Type*} [CommRing K] [CommRing R] [Algebra K R] (I : Ideal R) (a : R) :
    (Localization.Away a ⧸ I.map (algebraMap R (Localization.Away a))) ≃ₐ[K]
      Localization.Away (Ideal.Quotient.mk I a) where
  __ := (awayQuotientEquiv I a).toRingEquiv
  commutes' c := by
    change awayQuotientEquiv I a
      (Ideal.Quotient.mk _ (algebraMap R (Localization.Away a) (algebraMap K R c))) =
        algebraMap K (Localization.Away (Ideal.Quotient.mk I a)) c
    rw [awayQuotientEquiv_mk]
    rfl

theorem awayQuotientEquiv_invSelf
    {R : Type*} [CommRing R] (I : Ideal R) (a : R) :
    awayQuotientEquiv I a (Ideal.Quotient.mk _ (IsLocalization.Away.invSelf a)) =
      IsLocalization.Away.invSelf (Ideal.Quotient.mk I a) := by
  have h : IsUnit (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I a))
      (Ideal.Quotient.mk I a)) := IsLocalization.Away.algebraMap_isUnit _
  apply h.mul_left_cancel
  have hc := congrArg (awayQuotientEquiv I a)
    (congrArg (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away a))))
      (IsLocalization.Away.mul_invSelf (S := Localization.Away a) a))
  rw [map_mul, map_mul, map_one, map_one, awayQuotientEquiv_mk] at hc
  rw [hc, IsLocalization.Away.mul_invSelf]

theorem rationalPolynomialChartMap_awayQuotient_comp
    {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K) :
    let J := I.map (algebraMap _ (Localization.Away p0))
    (awayQuotientBaseEquiv (K := K) I p0).toAlgHom.comp
      ((Ideal.Quotient.mkₐ K J).comp (rationalPolynomialChartMap p0 p)) =
        MvPolynomial.aeval (fun i =>
          algebraMap _ (Localization.Away (Ideal.Quotient.mk I p0)) (Ideal.Quotient.mk I (p i)) *
            IsLocalization.Away.invSelf (Ideal.Quotient.mk I p0)) := by
  intro J
  apply MvPolynomial.algHom_ext
  intro i
  change awayQuotientEquiv I p0
    (Ideal.Quotient.mk J (rationalPolynomialChartMap p0 p (MvPolynomial.X i))) = _
  simp only [rationalPolynomialChartMap, MvPolynomial.aeval_X, map_mul]
  exact congrArg₂ (fun a b => a * b)
    (awayQuotientEquiv_mk I p0 (p i)) (awayQuotientEquiv_invSelf I p0)

end LinearStudy
