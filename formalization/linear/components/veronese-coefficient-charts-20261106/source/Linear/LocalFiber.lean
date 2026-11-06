module
public import Linear.CompletionQuotient
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.Submodule
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R : Type*} [CommRing R]

def localizationQuotientEquiv (I : Ideal R) (p : Ideal (R ⧸ I)) [p.IsPrime] :
    let P := p.comap (Ideal.Quotient.mk I)
    let A := Localization.AtPrime P
    (A ⧸ I.map (algebraMap R A)) ≃ₐ[R ⧸ I] Localization.AtPrime p := by
  let Q := R ⧸ I
  let P := p.comap (Ideal.Quotient.mk I)
  let A := Localization.AtPrime P
  let B := A ⧸ I.map (algebraMap R A)
  have hm : P.primeCompl.map (Ideal.Quotient.mk I) = p.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  let : IsLocalization p.primeCompl B := by
    rw [← hm]
    exact inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid Q P.primeCompl) B)
  exact IsLocalization.algEquiv p.primeCompl B (Localization.AtPrime p)

theorem localizationQuotientEquiv_mk (I : Ideal R) (p : Ideal (R ⧸ I)) [p.IsPrime] (r : R) :
    localizationQuotientEquiv I p
      (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime (p.comap (Ideal.Quotient.mk I))) r)) =
      algebraMap (R ⧸ I) (Localization.AtPrime p) (Ideal.Quotient.mk I r) := by
  exact (localizationQuotientEquiv I p).commutes (Ideal.Quotient.mk I r)

def localFiberCompletionQuotientEquiv [IsNoetherianRing R]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (p : Ideal (R ⧸ I)) [p.IsPrime] :
    let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    (C ⧸ (I.map (algebraMap R A)).map (algebraMap A C)) ≃+* Localization.AtPrime p := by
  let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
  let J := I.map (algebraMap R A)
  let B := A ⧸ J
  let e := localizationQuotientEquiv I p
  let : IsArtinianRing B := e.symm.toRingEquiv.isArtinianRing
  exact (artinianAmbientCompletionQuotientEquiv J).toRingEquiv.trans e.toRingEquiv

theorem localFiberCompletionQuotientEquiv_mk [IsNoetherianRing R]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (p : Ideal (R ⧸ I)) [p.IsPrime] (r : R) :
    let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    localFiberCompletionQuotientEquiv I p
      (Ideal.Quotient.mk _ (algebraMap A C (algebraMap R A r))) =
      algebraMap (R ⧸ I) (Localization.AtPrime p) (Ideal.Quotient.mk I r) := by
  let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
  let B := A ⧸ I.map (algebraMap R A)
  let : IsArtinianRing B := (localizationQuotientEquiv I p).symm.toRingEquiv.isArtinianRing
  unfold localFiberCompletionQuotientEquiv
  change localizationQuotientEquiv I p
    (artinianAmbientCompletionQuotientEquiv _
      (Ideal.Quotient.mk _ (algebraMap _ _ (algebraMap _ _ r)))) = _
  rw [artinianAmbientCompletionQuotientEquiv_mk, localizationQuotientEquiv_mk]

theorem local_fiber_socle_generator_of_completed_ambient [IsNoetherianRing R]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] (p : Ideal (R ⧸ I)) [p.IsPrime] (theta : R)
    (h : let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
      let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
      let Q := C ⧸ (I.map (algebraMap R A)).map (algebraMap A C)
      (nilradical Q).annihilator =
        Ideal.span {Ideal.Quotient.mk _ (algebraMap A C (algebraMap R A theta))}) :
    (nilradical (Localization.AtPrime p)).annihilator =
      Ideal.span {algebraMap (R ⧸ I) (Localization.AtPrime p) (Ideal.Quotient.mk I theta)} := by
  have hg := ringEquiv_nilradical_annihilator_generator
    (localFiberCompletionQuotientEquiv I p) _ h
  rwa [localFiberCompletionQuotientEquiv_mk] at hg

end LinearStudy
