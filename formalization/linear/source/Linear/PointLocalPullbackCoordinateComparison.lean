module
public import Linear.PointLocalCoordinateEquiv
public import Linear.GeneralLocalQuotientPullback
public import Mathlib.RingTheory.RingHom.Unramified
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace LinearStudy

/-- The genuine point-local quotient pullback commutes with independently
chosen source and target coordinates. The only diagram input is the actual
ambient ring-map identity; no local-map equality is assumed. -/
theorem generalPointLocalQuotientPullback_coordinate_commutes
    {R A T C : Type*} [CommRing R] [CommRing A] [CommRing T] [CommRing C]
    (I Q : Ideal R) (J P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (Q' : Ideal T) (P' : Ideal C) [Q'.IsPrime] [P'.IsPrime]
    (e : R ≃+* T) (d : A ≃+* C)
    (hQ : Q = Q'.comap e) (hP : P = P'.comap d)
    (φ : R →+* A) (ψ : T →+* C)
    (hQP : Q = P.comap φ) (hQ'P' : Q' = P'.comap ψ)
    (hφ : I.map φ ≤ J) (hψ : (I.map e.toRingHom).map ψ ≤ J.map d.toRingHom)
    (hd : d.toRingHom.comp φ = ψ.comp e.toRingHom) :
    (pointLocalCoordinateEquiv J P P' d hP).toRingHom.comp
        (generalPointLocalQuotientPullback I J P Q φ hQP hφ) =
      (generalPointLocalQuotientPullback (I.map e.toRingHom) (J.map d.toRingHom)
        P' Q' ψ hQ'P' hψ).comp (pointLocalCoordinateEquiv I Q Q' e hQ).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext Q.primeCompl
  apply RingHom.ext
  intro a
  change pointLocalCoordinateEquiv J P P' d hP
      (generalPointLocalQuotientPullback I J P Q φ hQP hφ
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime Q) a))) =
    generalPointLocalQuotientPullback (I.map e.toRingHom) (J.map d.toRingHom)
      P' Q' ψ hQ'P' hψ (pointLocalCoordinateEquiv I Q Q' e hQ
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime Q) a)))
  rw [generalPointLocalQuotientPullback_mk, pointLocalCoordinateEquiv_mk,
    pointLocalCoordinateEquiv_mk, generalPointLocalQuotientPullback_mk]
  exact congrArg (fun z => Ideal.Quotient.mk _ (algebraMap C (Localization.AtPrime P') z))
    (congrArg (fun f : R →+* C => f a) hd)

/-- Transport the original unramified local quotient map through the above
actual diagram, rather than supplying a new unramification assumption. -/
theorem generalPointLocalQuotientPullback_unramified_coordinates
    {R A T C : Type*} [CommRing R] [CommRing A] [CommRing T] [CommRing C]
    (I Q : Ideal R) (J P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (Q' : Ideal T) (P' : Ideal C) [Q'.IsPrime] [P'.IsPrime]
    (e : R ≃+* T) (d : A ≃+* C)
    (hQ : Q = Q'.comap e) (hP : P = P'.comap d)
    (φ : R →+* A) (ψ : T →+* C)
    (hQP : Q = P.comap φ) (hQ'P' : Q' = P'.comap ψ)
    (hφ : I.map φ ≤ J) (hψ : (I.map e.toRingHom).map ψ ≤ J.map d.toRingHom)
    (hd : d.toRingHom.comp φ = ψ.comp e.toRingHom)
    (h : (generalPointLocalQuotientPullback I J P Q φ hQP hφ).FormallyUnramified) :
    (generalPointLocalQuotientPullback (I.map e.toRingHom) (J.map d.toRingHom)
      P' Q' ψ hQ'P' hψ).FormallyUnramified := by
  have he : (pointLocalCoordinateEquiv J P P' d hP).toRingHom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_surjective (pointLocalCoordinateEquiv J P P' d hP).surjective
  have hc := h.comp he
  rw [generalPointLocalQuotientPullback_coordinate_commutes I Q J P Q' P' e d
    hQ hP φ ψ hQP hQ'P' hφ hψ hd] at hc
  exact hc.of_comp

end LinearStudy
