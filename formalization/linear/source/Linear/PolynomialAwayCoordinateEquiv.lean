module
public import Linear.ProjectiveRationalChart
public import Mathlib.RingTheory.Localization.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- The actual source coordinate equivalence extends across its nonzero
denominator, including the transformed denominator rather than a fresh ring. -/
def polynomialAwayCoordinateEquiv {K R T : Type*}
    [CommRing K] [CommRing R] [CommRing T] [Algebra K R] [Algebra K T]
    (e : R ≃ₐ[K] T) (a : R) : Localization.Away a ≃ₐ[K] Localization.Away (e a) :=
  IsLocalization.algEquivOfAlgEquiv _ _ e (Submonoid.map_powers e a)

theorem polynomialAwayCoordinateEquiv_algebraMap {K R T : Type*}
    [CommRing K] [CommRing R] [CommRing T] [Algebra K R] [Algebra K T]
    (e : R ≃ₐ[K] T) (a b : R) :
    polynomialAwayCoordinateEquiv e a (algebraMap R (Localization.Away a) b) =
      algebraMap T (Localization.Away (e a)) (e b) :=
  IsLocalization.algEquivOfAlgEquiv_eq (Submonoid.map_powers e a) b

theorem polynomialAwayCoordinateEquiv_invSelf {K R T : Type*}
    [CommRing K] [CommRing R] [CommRing T] [Algebra K R] [Algebra K T]
    (e : R ≃ₐ[K] T) (a : R) :
    polynomialAwayCoordinateEquiv e a (IsLocalization.Away.invSelf a) =
      IsLocalization.Away.invSelf (e a) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (e a)) (e a)
  apply hu.mul_left_cancel
  have h := congrArg (polynomialAwayCoordinateEquiv e a)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away a) a)
  rw [map_mul, polynomialAwayCoordinateEquiv_algebraMap, map_one] at h
  exact h.trans (IsLocalization.Away.mul_invSelf (S := Localization.Away (e a)) (e a)).symm

theorem polynomialAwayCoordinateEquiv_original_ideal {K R T : Type*}
    [CommRing K] [CommRing R] [CommRing T] [Algebra K R] [Algebra K T]
    (e : R ≃ₐ[K] T) (a : R) (I : Ideal R) :
    (I.map (algebraMap R (Localization.Away a))).map
        (polynomialAwayCoordinateEquiv e a).toRingHom =
      (I.map e.toRingHom).map (algebraMap T (Localization.Away (e a))) := by
  have he : (polynomialAwayCoordinateEquiv e a).toRingHom.comp
      (algebraMap R (Localization.Away a)) =
        (algebraMap T (Localization.Away (e a))).comp e.toRingHom := by
    ext b
    exact polynomialAwayCoordinateEquiv_algebraMap e a b
  rw [Ideal.map_map, he, Ideal.map_map]

/-- Source coordinates commute with the genuine rational pullback of the
original polynomial numerators, with the actual denominator inverted. -/
theorem rationalPolynomialChartMap_source_coordinate_equiv
    {K σ : Type*} [Field K]
    (e : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (p0 : MvPolynomial σ K) (p : σ → MvPolynomial σ K) :
    (polynomialAwayCoordinateEquiv e p0).toAlgHom.comp (rationalPolynomialChartMap p0 p) =
      rationalPolynomialChartMap (e p0) (fun i => e (p i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [rationalPolynomialChartMap, polynomialAwayCoordinateEquiv_algebraMap,
    polynomialAwayCoordinateEquiv_invSelf]

end LinearStudy
