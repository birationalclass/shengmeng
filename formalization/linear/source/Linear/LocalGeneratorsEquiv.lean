module
public import Linear.PolynomialLinearChange
public import Mathlib.RingTheory.Localization.AtPrime.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open scoped Matrix

theorem local_ideal_generators_under_ringEquiv {R T ι : Type*}
    [CommRing R] [CommRing T] (I P : Ideal R) [P.IsPrime]
    (Q : Ideal T) [Q.IsPrime] (e : R ≃+* T) (hP : P = Q.comap e)
    (G : ι → R)
    (hs : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    (I.map e.toRingHom).map (algebraMap _ (Localization.AtPrime Q)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime Q) (e (G i)))) := by
  have hm : P.primeCompl.map e = Q.primeCompl := by
    simpa only [← hP] using e.map_primeCompl_comap_eq Q
  let L := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q) e hm
  have hc : L.toRingHom.comp (algebraMap _ (Localization.AtPrime P)) =
      (algebraMap _ (Localization.AtPrime Q)).comp e.toRingHom := by
    apply RingHom.ext
    intro a
    exact IsLocalization.ringEquivOfRingEquiv_eq (j := e) hm a
  have h := congrArg (fun J : Ideal (Localization.AtPrime P) => J.map L.toRingHom) hs
  rw [Ideal.map_map, hc, ← Ideal.map_map, Ideal.map_span, ← Set.range_comp] at h
  have hf : (L.toRingHom ∘ fun i => algebraMap _ (Localization.AtPrime P) (G i)) =
      (fun i => algebraMap _ (Localization.AtPrime Q) (e (G i))) := by
    funext i
    exact IsLocalization.ringEquivOfRingEquiv_eq (j := e) hm (G i)
  rwa [hf] at h

theorem point_kernel_under_polynomialLinearChange {K σ : Type*}
    [Field K] [Fintype σ] [DecidableEq σ]
    (P : Matrix σ σ K) (hP : Matrix.det P ≠ 0) (x : σ → K) :
    RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom =
      (RingHom.ker (MvPolynomial.aeval (R := K) (P⁻¹ *ᵥ x)).toRingHom).comap
        (polynomialLinearChangeEquiv P hP).toRingHom := by
  have hx : P *ᵥ (P⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP),
      Matrix.one_mulVec]
  ext G
  change MvPolynomial.eval x G = 0 ↔
    MvPolynomial.eval (P⁻¹ *ᵥ x) (polynomialLinearChange P G) = 0
  rw [eval_polynomialLinearChange, hx]

/-- The original point-local generators remain generators of the actual
transformed ideal at the actual inverse-transformed point. -/
theorem polynomial_local_generators_under_linear_change {K σ ι : Type*}
    [Field K] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ K)) (x : σ → K)
    (P : Matrix σ σ K) (hP : Matrix.det P ≠ 0) (G : ι → MvPolynomial σ K)
    (hs : letI : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime :=
        RingHom.ker_isPrime _
      I.map (algebraMap _ (Localization.AtPrime
          (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom))) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime
          (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)) (G i)))) :
    letI : (RingHom.ker (MvPolynomial.aeval (R := K) (P⁻¹ *ᵥ x)).toRingHom).IsPrime :=
      RingHom.ker_isPrime _
    (I.map (polynomialLinearChangeEquiv P hP).toRingHom).map (algebraMap _
      (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) (P⁻¹ *ᵥ x)).toRingHom))) =
        Ideal.span (Set.range (fun i => algebraMap _
          (Localization.AtPrime (RingHom.ker (MvPolynomial.aeval (R := K) (P⁻¹ *ᵥ x)).toRingHom))
            (polynomialLinearChangeEquiv P hP (G i)))) := by
  let : (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).IsPrime := RingHom.ker_isPrime _
  let : (RingHom.ker (MvPolynomial.aeval (R := K) (P⁻¹ *ᵥ x)).toRingHom).IsPrime :=
    RingHom.ker_isPrime _
  exact local_ideal_generators_under_ringEquiv I _ _ (polynomialLinearChangeEquiv P hP).toRingEquiv
    (point_kernel_under_polynomialLinearChange P hP x) G hs

end LinearStudy
