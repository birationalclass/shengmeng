module
public import Linear.CompletionLocalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R S : Type*} [CommRing R] [CommRing S]

def completionCompatibleMap (I : Ideal R) (J : Ideal S)
    (q : (n : ℕ) → (R ⧸ I ^ n) →+* (S ⧸ J ^ n))
    (hq : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (q n) =
        (q m).comp (Ideal.Quotient.factorPow I h)) :
    AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n => (q n).comp (AdicCompletion.evalₐ I n).toRingHom) (by
      intro m n h
      apply RingHom.ext; intro x
      have ht := congrArg (fun f => f (AdicCompletion.evalₐ I n x)) (hq h)
      change Ideal.Quotient.factorPow J h (q n (AdicCompletion.evalₐ I n x)) = _
      rw [show Ideal.Quotient.factorPow J h (q n (AdicCompletion.evalₐ I n x)) =
        q m (Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x)) from ht]
      rw [completion_eval_naturality I h]
      rfl)

theorem completionCompatibleMap_eval (I : Ideal R) (J : Ideal S)
    (q : (n : ℕ) → (R ⧸ I ^ n) →+* (S ⧸ J ^ n))
    (hq : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (q n) =
        (q m).comp (Ideal.Quotient.factorPow I h))
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionCompatibleMap I J q hq x) =
      q n (AdicCompletion.evalₐ I n x) := by
  unfold completionCompatibleMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  · rfl
  · intro m n h
    apply RingHom.ext; intro x
    have ht := congrArg (fun f => f (AdicCompletion.evalₐ I n x)) (hq h)
    change Ideal.Quotient.factorPow J h (q n (AdicCompletion.evalₐ I n x)) = _
    rw [show Ideal.Quotient.factorPow J h (q n (AdicCompletion.evalₐ I n x)) =
      q m (Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x)) from ht]
    rw [completion_eval_naturality I h]
    rfl

theorem compatibleQuotientEquiv_symm (I : Ideal R) (J : Ideal S)
    (q : (n : ℕ) → (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n))
    (hq : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (q n).toRingHom =
        (q m).toRingHom.comp (Ideal.Quotient.factorPow I h))
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (q n).symm.toRingHom =
      (q m).symm.toRingHom.comp (Ideal.Quotient.factorPow J h) := by
  apply RingHom.ext; intro x
  apply (q m).injective
  have ht := congrArg (fun f => f ((q n).symm x)) (hq h)
  change Ideal.Quotient.factorPow J h (q n ((q n).symm x)) =
    q m (Ideal.Quotient.factorPow I h ((q n).symm x)) at ht
  change q m (Ideal.Quotient.factorPow I h ((q n).symm x)) =
    q m ((q m).symm (Ideal.Quotient.factorPow J h x))
  rw [RingEquiv.apply_symm_apply] at ht ⊢
  exact ht.symm

def completionEquivOfCompatibleQuotients (I : Ideal R) (J : Ideal S)
    (q : (n : ℕ) → (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n))
    (hq : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (q n).toRingHom =
        (q m).toRingHom.comp (Ideal.Quotient.factorPow I h)) :
    AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom
    (completionCompatibleMap I J (fun n => (q n).toRingHom) hq)
    (completionCompatibleMap J I (fun n => (q n).symm.toRingHom)
      (fun h => compatibleQuotientEquiv_symm I J q hq h))
    (by apply RingHom.ext; intro x; apply AdicCompletion.ext_evalₐ; intro n
        rw [RingHom.comp_apply, RingHom.id_apply, completionCompatibleMap_eval,
          completionCompatibleMap_eval]
        exact (q n).apply_symm_apply _)
    (by apply RingHom.ext; intro x; apply AdicCompletion.ext_evalₐ; intro n
        rw [RingHom.comp_apply, RingHom.id_apply, completionCompatibleMap_eval,
          completionCompatibleMap_eval]
        exact (q n).symm_apply_apply _)

theorem completionEquivOfCompatibleQuotients_eval (I : Ideal R) (J : Ideal S)
    (q : (n : ℕ) → (R ⧸ I ^ n) ≃+* (S ⧸ J ^ n))
    (hq : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow J h).comp (q n).toRingHom =
        (q m).toRingHom.comp (Ideal.Quotient.factorPow I h))
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionEquivOfCompatibleQuotients I J q hq x) =
      q n (AdicCompletion.evalₐ I n x) :=
  completionCompatibleMap_eval I J (fun n => (q n).toRingHom) hq n x

def completionCongrRingEquiv (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (he : J = I.map e.toRingHom) : AdicCompletion I R ≃+* AdicCompletion J S :=
  let q (n : ℕ) := Ideal.quotientEquiv (I ^ n) (J ^ n) e (by rw [he, Ideal.map_pow]; rfl)
  completionEquivOfCompatibleQuotients I J q (by
    intro m n h
    apply RingHom.ext; intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [q, Ideal.quotientEquiv])

theorem completionCongrRingEquiv_of (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (he : J = I.map e.toRingHom) (r : R) :
    completionCongrRingEquiv e I J he (AdicCompletion.of I R r) =
      AdicCompletion.of J S (e r) := by
  apply AdicCompletion.ext_evalₐ; intro n
  unfold completionCongrRingEquiv
  rw [completionEquivOfCompatibleQuotients_eval, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  · rfl
  · intro m n h
    apply RingHom.ext; intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.quotientEquiv]

end LinearStudy
