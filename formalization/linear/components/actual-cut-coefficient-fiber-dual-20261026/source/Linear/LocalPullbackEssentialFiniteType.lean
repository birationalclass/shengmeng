module
public import Linear.GeneralLocalQuotientPullback
public import Mathlib.RingTheory.RingHom.EssFiniteType
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K R A : Type*} [CommRing K] [CommRing R] [CommRing A]
  [Algebra K R] [Algebra K A]

theorem generalPointLocalQuotientPullback_scalar_comp
    (I : Ideal R) (J P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →ₐ[K] A) (hQP : Q = P.comap φ.toRingHom) (hφ : I.map φ.toRingHom ≤ J) :
    (generalPointLocalQuotientPullback I J P Q φ.toRingHom hQP hφ).comp
      (algebraMap K (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))) =
      algebraMap K (Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P))) := by
  apply RingHom.ext
  intro k
  change generalPointLocalQuotientPullback I J P Q φ.toRingHom hQP hφ
    (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime Q) (algebraMap K R k))) =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime P) (algebraMap K A k))
  rw [generalPointLocalQuotientPullback_mk]
  exact congrArg (fun a => Ideal.Quotient.mk _
    (algebraMap A (Localization.AtPrime P) a)) (φ.commutes k)

/-- Essential finite type for this actual local quotient map follows from
the finite-type source over the ground ring and compatibility of scalars. -/
theorem generalPointLocalQuotientPullback_essFiniteType
    [Algebra.EssFiniteType K A]
    (I : Ideal R) (J P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →ₐ[K] A) (hQP : Q = P.comap φ.toRingHom) (hφ : I.map φ.toRingHom ≤ J) :
    (generalPointLocalQuotientPullback I J P Q φ.toRingHom hQP hφ).EssFiniteType := by
  let B := Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P))
  letI : Algebra.EssFiniteType A (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_isLocalization (Localization.AtPrime P) P.primeCompl
  letI : Algebra.EssFiniteType K (Localization.AtPrime P) :=
    Algebra.EssFiniteType.comp K A (Localization.AtPrime P)
  letI : Algebra.EssFiniteType K B := inferInstance
  apply RingHom.EssFiniteType.of_comp
    (algebraMap K (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))))
  rw [generalPointLocalQuotientPullback_scalar_comp I J P Q φ hQP hφ,
    RingHom.essFiniteType_algebraMap]
  infer_instance

end LinearStudy
