module
public import Linear.PolynomialSmoothReduction
public import Mathlib.RingTheory.Localization.AtPrime.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem local_pullback_ideal_le {R : Type*} [CommRing R]
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →+* R) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ I) :
    I.map (algebraMap R (Localization.AtPrime Q)) ≤
      (I.map (algebraMap R (Localization.AtPrime P))).comap
        (Localization.localRingHom Q P φ hQP) := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_map]
  have hcomp : (Localization.localRingHom Q P φ hQP).comp
      (algebraMap R (Localization.AtPrime Q)) =
      (algebraMap R (Localization.AtPrime P)).comp φ := by
    apply RingHom.ext
    intro a
    exact Localization.localRingHom_to_map Q P φ hQP a
  rw [hcomp, ← Ideal.map_map]
  exact Ideal.map_mono hφ

def pointLocalQuotientPullback {R : Type*} [CommRing R]
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →+* R) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ I) :
    (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) →+*
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) :=
  Ideal.quotientMap _ (Localization.localRingHom Q P φ hQP)
    (local_pullback_ideal_le I P Q φ hQP hφ)

theorem pointLocalQuotientPullback_polynomial {R : Type*} [CommRing R]
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →+* R) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ I) (a : R) :
    pointLocalQuotientPullback I P Q φ hQP hφ
      (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime Q) a)) =
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) (φ a)) := by
  unfold pointLocalQuotientPullback
  rw [Ideal.quotientMap_mk, Localization.localRingHom_to_map]

theorem local_quotient_map_isLocalHom {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (I : Ideal R) (J : Ideal S) [Nontrivial (S ⧸ J)]
    (φ : R →+* S) [IsLocalHom φ] (h : I ≤ J.comap φ) :
    IsLocalHom (Ideal.quotientMap J φ h) := by
  let : IsLocalHom (Ideal.Quotient.mk J) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
  rw [Ideal.quotientMap_mk] at ha
  exact (Ideal.Quotient.mk I).isUnit_map
    (isUnit_of_map_unit φ b (isUnit_of_map_unit (Ideal.Quotient.mk J) (φ b) ha))

theorem pointLocalQuotientPullback_isLocalHom {R : Type*} [CommRing R]
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [Nontrivial (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))]
    (φ : R →+* R) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ I) :
    IsLocalHom (pointLocalQuotientPullback I P Q φ hQP hφ) :=
  local_quotient_map_isLocalHom _ _ _ _

theorem polynomial_pullback_point_comap {K σ : Type*} [CommRing K]
    (F : σ → MvPolynomial σ K) (x : σ → K) :
    RingHom.ker (MvPolynomial.aeval (R := K) (fun i => MvPolynomial.eval x (F i))).toRingHom =
      (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).comap
        (MvPolynomial.aeval F).toRingHom := by
  rw [RingHom.comap_ker]
  congr 1
  apply RingHom.ext
  intro a
  exact MvPolynomial.eval_assoc F x a

theorem smooth_local_quotient_pullback_reduction {K : Type*} [Field K]
    {r c : ℕ} [Nonempty (Fin c)]
    (I P Q : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime] [Q.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (F : Fin r ⊕ Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hQP : Q = P.comap (MvPolynomial.aeval F).toRingHom)
    (hF : I.map (MvPolynomial.aeval F).toRingHom ≤ I)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x
      (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (a : MvPolynomial (Fin r ⊕ Fin c) K) :
    polynomialSmoothLocalQuotientReduction I P x hP G hG hJ hlocal
      (pointLocalQuotientPullback I P Q (MvPolynomial.aeval F).toRingHom hQP hF
        (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime Q) a))) =
      polynomialSmoothReducedMap x G hG hJ (MvPolynomial.aeval F a) := by
  rw [pointLocalQuotientPullback_polynomial,
    polynomialSmoothLocalQuotientReduction_mk, polynomialSmoothPointLocalReduction_polynomial]
  rfl

end LinearStudy
