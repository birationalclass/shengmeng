module
public import Linear.ArtinianCompletion
public import Linear.ArbitraryParameterJacobian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Quotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R : Type*} [CommRing R]

theorem completion_eval_kernel (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  trans x ∈ (AdicCompletion.eval I R n).ker
  · have eq : I ^ n * ⊤ = I ^ n := Ideal.mul_top _
    have hi : Function.Injective (Ideal.Quotient.factor (le_of_eq eq)) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    simpa [← AdicCompletion.factor_eval_eq_evalₐ] using map_eq_zero_iff _ hi
  · simp [← AdicCompletion.pow_smul_top_eq_ker_eval hI]

def completionQuotientMap (I J : Ideal R) (n : ℕ) (hn : I ^ n ≤ J) :
    AdicCompletion I R →ₐ[R] R ⧸ J :=
  (Ideal.Quotient.factorₐ R hn).comp (AdicCompletion.evalₐ I n)

theorem completionQuotientMap_surjective (I J : Ideal R) (n : ℕ) (hn : I ^ n ≤ J) :
    Function.Surjective (completionQuotientMap I J n hn) :=
  (Ideal.Quotient.factor_surjective hn).comp (AdicCompletion.surjective_evalₐ I n)

theorem completionQuotientMap_kernel (I J : Ideal R) (hI : I.FG)
    (n : ℕ) (hn : I ^ n ≤ J) :
    RingHom.ker (completionQuotientMap I J n hn).toRingHom =
      J.map (algebraMap R (AdicCompletion I R)) := by
  let α := algebraMap R (AdicCompletion I R)
  let F := completionQuotientMap I J n hn
  have hle : J.map α ≤ RingHom.ker F.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change F (α r) = 0
    rw [F.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  apply le_antisymm ?_ hle
  intro x hx
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hrJ : r ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change F x = 0 at hx
    simpa [F, completionQuotientMap, ← hr] using hx
  have he : x - α r ∈ RingHom.ker (AdicCompletion.evalₐ I n).toRingHom := by
    change AdicCompletion.evalₐ I n (x - α r) = 0
    rw [map_sub, (AdicCompletion.evalₐ I n).commutes]
    exact sub_eq_zero.mpr hr.symm
  rw [completion_eval_kernel I hI n] at he
  have hd : x - α r ∈ J.map α := Ideal.map_mono hn he
  simpa using (J.map α).add_mem hd (Ideal.mem_map_of_mem α hrJ)

def completionQuotientEquiv (I J : Ideal R) (hI : I.FG)
    (n : ℕ) (hn : I ^ n ≤ J) :
    ((AdicCompletion I R) ⧸ (J.map (algebraMap R (AdicCompletion I R)))) ≃ₐ[R] (R ⧸ J) :=
  (Ideal.quotientEquivAlgOfEq R (completionQuotientMap_kernel I J hI n hn).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (completionQuotientMap_surjective I J n hn))

theorem completionQuotientEquiv_mk (I J : Ideal R) (hI : I.FG)
    (n : ℕ) (hn : I ^ n ≤ J) (r : R) :
    completionQuotientEquiv I J hI n hn
      (Ideal.Quotient.mk _ (algebraMap R (AdicCompletion I R) r)) =
      Ideal.Quotient.mk J r := by
  simp [completionQuotientEquiv, completionQuotientMap]

def artinianAmbientCompletionQuotientEquiv [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) [IsArtinianRing (R ⧸ J)] :
    ((AdicCompletion (IsLocalRing.maximalIdeal R) R) ⧸
      (J.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))) ≃ₐ[R] (R ⧸ J) :=
  let h := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  completionQuotientEquiv _ J (IsNoetherian.noetherian _) h.choose h.choose_spec

theorem artinianAmbientCompletionQuotientEquiv_mk [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) [IsArtinianRing (R ⧸ J)] (r : R) :
    artinianAmbientCompletionQuotientEquiv J
      (Ideal.Quotient.mk _ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r)) =
      Ideal.Quotient.mk J r := by
  let h := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient J
  exact completionQuotientEquiv_mk _ J (IsNoetherian.noetherian _) h.choose h.choose_spec r

theorem ringEquiv_nilradical_annihilator_generator {A C : Type*}
    [CommRing A] [CommRing C] (e : A ≃+* C) (theta : A)
    (h : (nilradical A).annihilator = Ideal.span {theta}) :
    (nilradical C).annihilator = Ideal.span {e theta} := by
  have ht : ∀ x : A, x ∈ (nilradical A).annihilator ↔
      e x ∈ (nilradical C).annihilator := by
    intro x
    simpa only [Submodule.mem_annihilator, Annihilates, smul_eq_mul, mul_comm] using
      annihilates_nilradical_ringEquiv e x
  ext x
  rw [← e.apply_symm_apply x, ← ht, h]
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e b, ?_⟩
    rw [← map_mul, hb]
  · intro hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.symm b, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply]
    simpa only [e.apply_symm_apply] using hb

theorem artinian_ambient_socle_generator_descends [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) [IsArtinianRing (R ⧸ J)] (theta : R)
    (h : let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
      let Q := C ⧸ J.map (algebraMap R C)
      (nilradical Q).annihilator =
        Ideal.span {Ideal.Quotient.mk _ (algebraMap R C theta)}) :
    (nilradical (R ⧸ J)).annihilator = Ideal.span {Ideal.Quotient.mk J theta} := by
  have hg := ringEquiv_nilradical_annihilator_generator
    (artinianAmbientCompletionQuotientEquiv J).toRingEquiv _ h
  change (nilradical (R ⧸ J)).annihilator = Ideal.span {
    artinianAmbientCompletionQuotientEquiv J
      (Ideal.Quotient.mk _ (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) theta))} at hg
  rwa [artinianAmbientCompletionQuotientEquiv_mk] at hg

end LinearStudy
