module
public import Linear.CompletionQuotient
public import Mathlib.RingTheory.Localization.AtPrime.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]

theorem primePowerQuotientEquiv_naturality {m n : ℕ} (h : m ≤ n) :
    let S := Localization.AtPrime p
    let q (k : ℕ) := IsLocalization.AtPrime.equivQuotMaximalIdealPow p S k
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal S) h)).comp
      (q n).toAlgHom =
      (q m).toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := p) h)) := by
  apply (AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective R (p ^ n))).mp
  ext

theorem primePowerQuotientEquiv_symm_naturality {m n : ℕ} (h : m ≤ n) :
    let S := Localization.AtPrime p
    let q (k : ℕ) := IsLocalization.AtPrime.equivQuotMaximalIdealPow p S k
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := p) h)).comp
      (q n).symm.toAlgHom =
      (q m).symm.toAlgHom.comp
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := IsLocalRing.maximalIdeal S) h)) := by
  let S := Localization.AtPrime p
  let q (k : ℕ) := IsLocalization.AtPrime.equivQuotMaximalIdealPow p S k
  ext x
  apply (q m).injective
  have ht := congrArg (fun f => f ((q n).symm x)) (primePowerQuotientEquiv_naturality p h)
  simpa only [q, S, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply] using ht.symm

theorem completion_eval_naturality (I : Ideal R) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨z, rfl⟩ := AdicCompletion.mk_surjective I R x
  change Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n (AdicCompletion.mkₐ I z)) =
    AdicCompletion.evalₐ I m (AdicCompletion.mkₐ I z)
  simpa only [AdicCompletion.evalₐ_mkₐ, Ideal.Quotient.factor_mk] using
    AdicCompletion.Ideal.mk_eq_mk I h z

theorem completionLocalizationForward_compatible {m n : ℕ} (h : m ≤ n) :
    let S := Localization.AtPrime p
    let f (n : ℕ) := (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).toRingHom.comp
      (AdicCompletion.evalₐ p n).toRingHom
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal S) h).comp (f n) = f m := by
  let S := Localization.AtPrime p
  let q (n : ℕ) := IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n
  let f (n : ℕ) := (q n).toRingHom.comp (AdicCompletion.evalₐ p n).toRingHom
  ext x
  have ht := congrArg (fun g => g (AdicCompletion.evalₐ p n x))
      (primePowerQuotientEquiv_naturality p h)
  change Ideal.Quotient.factorPow _ h ((q n) (AdicCompletion.evalₐ p n x)) = _
  rw [show Ideal.Quotient.factorPow _ h ((q n) (AdicCompletion.evalₐ p n x)) =
      q m (Ideal.Quotient.factorPow p h (AdicCompletion.evalₐ p n x)) from ht]
  rw [completion_eval_naturality p h]
  rfl

theorem completionLocalizationBackward_compatible {m n : ℕ} (h : m ≤ n) :
    let S := Localization.AtPrime p
    let f (n : ℕ) := (IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n).symm.toRingHom.comp
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n).toRingHom
    (Ideal.Quotient.factorPow p h).comp (f n) = f m := by
  let S := Localization.AtPrime p
  let q (n : ℕ) := IsLocalization.AtPrime.equivQuotMaximalIdealPow p S n
  let f (n : ℕ) := (q n).symm.toRingHom.comp
    (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n).toRingHom
  ext x
  have ht := congrArg (fun g => g (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n x))
      (primePowerQuotientEquiv_symm_naturality p h)
  change Ideal.Quotient.factorPow p h ((q n).symm
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n x)) = _
  rw [show Ideal.Quotient.factorPow p h ((q n).symm
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n x)) =
      (q m).symm (Ideal.Quotient.factorPow _ h
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) n x)) from ht]
  rw [completion_eval_naturality _ h]
  rfl

def completionLocalizationForward :
    AdicCompletion p R →+* AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :=
  AdicCompletion.liftRingHom _
    (fun n => (IsLocalization.AtPrime.equivQuotMaximalIdealPow p (Localization.AtPrime p) n).toRingHom.comp
      (AdicCompletion.evalₐ p n).toRingHom)
    (fun h => completionLocalizationForward_compatible p h)

def completionLocalizationBackward :
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) →+*
      AdicCompletion p R :=
  AdicCompletion.liftRingHom p
    (fun n => (IsLocalization.AtPrime.equivQuotMaximalIdealPow p (Localization.AtPrime p) n).symm.toRingHom.comp
      (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) n).toRingHom)
    (fun h => completionLocalizationBackward_compatible p h)

theorem completionLocalizationForward_eval (n : ℕ) (x : AdicCompletion p R) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) n
      (completionLocalizationForward p x) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow p (Localization.AtPrime p) n
        (AdicCompletion.evalₐ p n x) := by
  unfold completionLocalizationForward
  exact AdicCompletion.evalₐ_liftRingHom _ _
    (fun h => completionLocalizationForward_compatible p h) n x

theorem completionLocalizationBackward_eval (n : ℕ)
    (x : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) :
    AdicCompletion.evalₐ p n (completionLocalizationBackward p x) =
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow p (Localization.AtPrime p) n).symm
        (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) n x) := by
  unfold completionLocalizationBackward
  exact AdicCompletion.evalₐ_liftRingHom _ _
    (fun h => completionLocalizationBackward_compatible p h) n x

def completionLocalizationEquiv :
    AdicCompletion p R ≃+* AdicCompletion
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :=
  RingEquiv.ofRingHom (completionLocalizationForward p) (completionLocalizationBackward p)
    (by apply RingHom.ext; intro x; apply AdicCompletion.ext_evalₐ; intro n
        rw [RingHom.comp_apply, RingHom.id_apply, completionLocalizationForward_eval,
          completionLocalizationBackward_eval, AlgEquiv.apply_symm_apply])
    (by apply RingHom.ext; intro x; apply AdicCompletion.ext_evalₐ; intro n
        rw [RingHom.comp_apply, RingHom.id_apply, completionLocalizationBackward_eval,
          completionLocalizationForward_eval, AlgEquiv.symm_apply_apply])

theorem completionLocalizationEquiv_of (r : R) :
    completionLocalizationEquiv p (AdicCompletion.of p R r) =
      AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ _ n (completionLocalizationForward p _) = _
  rw [completionLocalizationForward_eval, AdicCompletion.evalₐ_of,
    IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk, AdicCompletion.evalₐ_of]

end LinearStudy
