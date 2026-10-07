module
public import Linear.GeneralLocalQuotientPullback
public import Linear.ProjectiveRationalChart
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- Localizing an open affine chart at a point gives the original point
local ring, including its actual quotient ideal. -/
def localizedPointQuotientEquiv {R : Type*} [CommRing R]
    (M : Submonoid R) (I : Ideal R) (P : Ideal (Localization M)) [P.IsPrime] :
    (Localization.AtPrime (P.comap (algebraMap R (Localization M))) ⧸
      I.map (algebraMap R (Localization.AtPrime (P.comap (algebraMap R (Localization M)))))) ≃+*
    (Localization.AtPrime P ⧸ (I.map (algebraMap R (Localization M))).map
      (algebraMap (Localization M) (Localization.AtPrime P))) := by
  let E := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P
  have he : E.toRingHom.comp (algebraMap R (Localization.AtPrime
      (P.comap (algebraMap R (Localization M))))) =
      (algebraMap (Localization M) (Localization.AtPrime P)).comp
        (algebraMap R (Localization M)) := by
    apply RingHom.ext
    intro a
    change E (algebraMap R (Localization.AtPrime
      (P.comap (algebraMap R (Localization M)))) a) =
        algebraMap (Localization M) (Localization.AtPrime P) (algebraMap R (Localization M) a)
    exact (E.commutes a).trans
      (IsScalarTower.algebraMap_apply R (Localization M) (Localization.AtPrime P) a)
  have hi : (I.map (algebraMap R (Localization M))).map
      (algebraMap (Localization M) (Localization.AtPrime P)) =
      (I.map (algebraMap R (Localization.AtPrime
        (P.comap (algebraMap R (Localization M)))))).map E.toRingHom := by
    rw [Ideal.map_map, Ideal.map_map, he]
  exact Ideal.quotientEquiv _ _ E.toRingEquiv hi

theorem localizedPointQuotientEquiv_mk {R : Type*} [CommRing R]
    (M : Submonoid R) (I : Ideal R) (P : Ideal (Localization M)) [P.IsPrime] (a : R) :
    localizedPointQuotientEquiv M I P
      (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime
        (P.comap (algebraMap R (Localization M)))) a)) =
      Ideal.Quotient.mk _ (algebraMap (Localization M) (Localization.AtPrime P)
        (algebraMap R (Localization M) a)) := by
  unfold localizedPointQuotientEquiv
  rw [Ideal.quotientEquiv_mk]
  congr 1
  exact ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P).commutes a).trans
    (IsScalarTower.algebraMap_apply R (Localization M) (Localization.AtPrime P) a)

theorem polynomialAwayPointEvaluation_point_comap {K σ : Type*} [Field K]
    (x : σ → K) (p0 : MvPolynomial σ K) (hp0 : MvPolynomial.eval x p0 ≠ 0) :
    (RingHom.ker (polynomialAwayPointEvaluation x p0 hp0).toRingHom).comap
      (algebraMap _ (Localization.Away p0)) =
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
  rw [RingHom.comap_ker]
  congr 1
  apply RingHom.ext
  intro a
  exact polynomialAwayPointEvaluation_algebraMap x p0 hp0 a

end LinearStudy
