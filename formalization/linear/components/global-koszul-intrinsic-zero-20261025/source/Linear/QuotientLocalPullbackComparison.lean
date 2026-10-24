module
public import Linear.LocalFiber
public import Linear.GeneralLocalQuotientPullback
public import Linear.GenericUnramifiedOpen
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

/-- The ambient local quotient pullback is the genuine variety-local pullback,
under the canonical localization/quotient comparisons. -/
theorem quotientLocalPullback_comparison
    {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (J : Ideal A) (φ : R →+* A) (hφ : I.map φ ≤ J)
    (P : Ideal (A ⧸ J)) [P.IsPrime] :
    let ψ := Ideal.quotientMap J φ (Ideal.map_le_iff_le_comap.mp hφ)
    let Q := P.comap ψ
    let p := P.comap (Ideal.Quotient.mk J)
    let q := Q.comap (Ideal.Quotient.mk I)
    (localizationQuotientEquiv J P).toRingHom.comp
      (generalPointLocalQuotientPullback I J p q φ (by ext r; rfl) hφ) =
      (Localization.localRingHom Q P ψ rfl).comp
        (localizationQuotientEquiv I Q).toRingHom := by
  intro ψ Q p q
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext q.primeCompl
  apply RingHom.ext
  intro a
  change localizationQuotientEquiv J P
      (generalPointLocalQuotientPullback I J p q φ _ hφ
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime q) a))) =
    Localization.localRingHom Q P ψ rfl
      (localizationQuotientEquiv I Q
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime q) a)))
  rw [generalPointLocalQuotientPullback_mk, localizationQuotientEquiv_mk,
    localizationQuotientEquiv_mk, Localization.localRingHom_to_map]
  rfl

theorem quotientLocalPullback_formallyUnramified
    {R A : Type*} [CommRing R] [CommRing A]
    (I : Ideal R) (J : Ideal A) (φ : R →+* A) (hφ : I.map φ ≤ J)
    (P : Ideal (A ⧸ J)) [P.IsPrime]
    (hP : let ψ := Ideal.quotientMap J φ (Ideal.map_le_iff_le_comap.mp hφ)
      (Localization.localRingHom (P.comap ψ) P ψ rfl).FormallyUnramified) :
    let ψ := Ideal.quotientMap J φ (Ideal.map_le_iff_le_comap.mp hφ)
    let Q := P.comap ψ
    let p := P.comap (Ideal.Quotient.mk J)
    let q := Q.comap (Ideal.Quotient.mk I)
    (generalPointLocalQuotientPullback I J p q φ (by ext r; rfl) hφ).FormallyUnramified := by
  intro ψ Q p q
  let E := localizationQuotientEquiv J P
  let D := localizationQuotientEquiv I Q
  let Φ := generalPointLocalQuotientPullback I J p q φ (by ext r; rfl) hφ
  have hD : D.toRingHom.FormallyUnramified := RingHom.FormallyUnramified.of_surjective D.surjective
  have hc := hD.comp hP
  have he := quotientLocalPullback_comparison I J φ hφ P
  change E.toRingHom.comp Φ = (Localization.localRingHom Q P ψ rfl).comp D.toRingHom at he
  rw [← he] at hc
  have hs : E.symm.toRingHom.FormallyUnramified := RingHom.FormallyUnramified.of_surjective E.symm.surjective
  have hc' := hc.comp hs
  have he' : E.symm.toRingHom.comp (E.toRingHom.comp Φ) = Φ := by
    ext a
    exact E.symm_apply_apply (Φ a)
  rwa [he'] at hc'

end LinearStudy
