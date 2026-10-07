module
public import Linear.ProjectiveCoordinateRatioMap
public import Mathlib.RingTheory.Localization.Ideal
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem localization_lift_kernel
    {R B F : Type*} [CommRing R] [CommRing B] [CommRing F]
    (M : Submonoid R) [Algebra R B] [IsLocalization M B]
    (φ : R →+* F) (hu : ∀ y : M, IsUnit (φ y)) :
    RingHom.ker (IsLocalization.lift (S := B) hu) =
      (RingHom.ker φ).map (algebraMap R B) := by
  have he : (RingHom.ker (IsLocalization.lift (S := B) hu)).under R =
      RingHom.ker φ := by
    change (RingHom.ker (IsLocalization.lift (S := B) hu)).comap (algebraMap R B) = _
    rw [RingHom.comap_ker, IsLocalization.lift_comp]
  rw [← IsLocalization.map_under M B (RingHom.ker (IsLocalization.lift (S := B) hu)), he]

theorem projectiveRatioPolynomialMap_kernel
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    letI := V.prime
    RingHom.ker (coordinateRatioPolynomialMap (projectiveConeFractionCoordinates V)).toRingHom =
      V.affineIdeal := by
  letI := V.prime
  let R := CoordinateRing n
  let A := R ⧸ V.ideal.toIdeal
  let F := FractionRing A
  let X₀ : R := MvPolynomial.X 0
  let B := Localization.Away X₀
  let φ : R →ₐ[ℂ] F := MvPolynomial.aeval (projectiveConeFractionCoordinates V)
  have hφ : φ = (IsScalarTower.toAlgHom ℂ A F).comp (Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal) := by
    apply AlgHom.ext
    intro H
    exact projectiveConeFractionCoordinates_aeval V H
  have hk : RingHom.ker φ.toRingHom = V.ideal.toIdeal := by
    rw [hφ]
    change RingHom.ker ((algebraMap A F).comp (Ideal.Quotient.mk V.ideal.toIdeal)) = _
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective A F), Ideal.mk_ker]
  have hn : φ X₀ ≠ 0 := by
    change MvPolynomial.aeval (projectiveConeFractionCoordinates V) (MvPolynomial.X 0) ≠ 0
    rw [MvPolynomial.aeval_X]
    exact projectiveConeFractionCoordinates_zero_ne_zero V x hx
  have hu : IsUnit (φ X₀) := isUnit_iff_ne_zero.mpr hn
  let ψ : B →ₐ[ℂ] F := IsLocalization.Away.liftAlgHom X₀ (f := φ) hu
  have hψ : RingHom.ker ψ.toRingHom =
      V.ideal.toIdeal.map (algebraMap R B) := by
    have he : (RingHom.ker ψ.toRingHom).under R = RingHom.ker φ.toRingHom := by
      change (RingHom.ker ψ.toRingHom).comap (algebraMap R B) = _
      rw [RingHom.comap_ker]
      have hc : ψ.toRingHom.comp (algebraMap R B) = φ.toRingHom :=
        IsLocalization.Away.lift_comp X₀ hu
      rw [hc]
    rw [← IsLocalization.map_under (Submonoid.powers X₀) B (RingHom.ker ψ.toRingHom), he, hk]
  have hl : ψ (IsLocalization.Away.invSelf X₀ (S := B)) = (φ X₀)⁻¹ := by
    apply mul_left_cancel₀ hn
    rw [mul_inv_cancel₀ hn]
    have hm := congrArg ψ (IsLocalization.Away.mul_invSelf X₀ (S := B))
    change ψ ((algebraMap R B X₀) * IsLocalization.Away.invSelf X₀) = ψ 1 at hm
    rw [map_mul, map_one,
      show ψ (algebraMap R B X₀) = φ X₀ from IsLocalization.Away.lift_eq X₀ hu X₀] at hm
    exact hm
  have hc : ψ.comp (projectiveChartLocalizationMap (K := ℂ) (n := n)) =
      coordinateRatioPolynomialMap (projectiveConeFractionCoordinates V) := by
    apply MvPolynomial.algHom_ext
    intro i
    change ψ (MvPolynomial.aeval (fun j : Fin n =>
      algebraMap R B (MvPolynomial.X j.succ) * IsLocalization.Away.invSelf X₀)
        (MvPolynomial.X i)) =
      MvPolynomial.aeval (fun j : Fin n => projectiveConeFractionCoordinates V j.succ /
        projectiveConeFractionCoordinates V 0) (MvPolynomial.X i)
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_mul, hl]
    rw [show ψ (algebraMap R B (MvPolynomial.X i.succ)) = φ (MvPolynomial.X i.succ) from
      IsLocalization.Away.lift_eq X₀ hu _]
    rw [show φ (MvPolynomial.X i.succ) = projectiveConeFractionCoordinates V i.succ from
      MvPolynomial.aeval_X _ _,
      show φ X₀ = projectiveConeFractionCoordinates V 0 from MvPolynomial.aeval_X _ _]
    exact (div_eq_mul_inv _ _).symm
  rw [← hc]
  change RingHom.ker (ψ.toRingHom.comp projectiveChartLocalizationMap.toRingHom) = _
  rw [← RingHom.comap_ker, hψ,
    projectiveChartLocalizationMap_comap_ideal V.ideal.toIdeal V.ideal.isHomogeneous]
  rfl

end LinearStudy
