module
public import Linear.LocalQuotientPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy

theorem general_local_pullback_ideal_le {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (J P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →+* A) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ J) :
    I.map (algebraMap R (Localization.AtPrime Q)) ≤
      (J.map (algebraMap A (Localization.AtPrime P))).comap
        (Localization.localRingHom Q P φ hQP) := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_map]
  have hcomp : (Localization.localRingHom Q P φ hQP).comp
      (algebraMap R (Localization.AtPrime Q)) =
      (algebraMap A (Localization.AtPrime P)).comp φ := by
    apply RingHom.ext
    intro a
    exact Localization.localRingHom_to_map Q P φ hQP a
  rw [hcomp, ← Ideal.map_map]
  exact Ideal.map_mono hφ

/-- Actual target and source rings and ideals may differ, as they do for
projective coordinate ratios landing in a denominator localization. -/
def generalPointLocalQuotientPullback {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (J P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →+* A) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ J) :
    (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) →+*
      (Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P))) :=
  Ideal.quotientMap _ (Localization.localRingHom Q P φ hQP)
    (general_local_pullback_ideal_le I J P Q φ hQP hφ)

theorem generalPointLocalQuotientPullback_mk {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (J P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (φ : R →+* A) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ J) (a : R) :
    generalPointLocalQuotientPullback I J P Q φ hQP hφ
      (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime Q) a)) =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime P) (φ a)) := by
  unfold generalPointLocalQuotientPullback
  rw [Ideal.quotientMap_mk, Localization.localRingHom_to_map]

theorem generalPointLocalQuotientPullback_isLocalHom {R A : Type*}
    [CommRing R] [CommRing A]
    (I : Ideal R) (J P : Ideal A) (Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    [Nontrivial (Localization.AtPrime P ⧸ J.map (algebraMap A (Localization.AtPrime P)))]
    (φ : R →+* A) (hQP : Q = P.comap φ) (hφ : I.map φ ≤ J) :
    IsLocalHom (generalPointLocalQuotientPullback I J P Q φ hQP hφ) :=
  local_quotient_map_isLocalHom _ _ _ _

end LinearStudy
