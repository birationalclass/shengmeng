module
public import Linear.LocalizedAnnihilator
public import Linear.SocleTransport
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.Tactic
/-! Nilpotent-adic completeness is proved from stabilization of the adic filtration. An actual Artinian local ring is canonically algebra-isomorphic to its maximal-ideal adic completion. Socle generation in that completion descends through this constructed isomorphism. Completion of an ambient quotient still needs its separate exactness comparison. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R : Type*} [CommRing R]

theorem isAdicComplete_of_nilpotent_ideal (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] (hI : IsNilpotent I) :
    IsAdicComplete I M := by
  obtain ⟨N, hN⟩ := hI
  have hzero : (I ^ N • ⊤ : Submodule R M) = ⊥ := by
    simp only [hN, Ideal.zero_eq_bot, Submodule.bot_smul]
  refine { haus' := ?haus, prec' := ?prec }
  case haus =>
    intro x hx
    have hh := hx N
    rwa [hzero, SModEq.bot] at hh
  case prec =>
    intro f hf
    refine ⟨f N, ?_⟩
    intro n
    by_cases hn : n ≤ N
    · exact hf hn
    · have hNn : N ≤ n := by omega
      have hh := hf hNn
      rw [hzero, SModEq.bot] at hh
      rw [← hh]

theorem artinian_local_nilradical_eq_maximalIdeal [IsArtinianRing R] [IsLocalRing R] :
    nilradical R = IsLocalRing.maximalIdeal R := by
  rw [IsArtinianRing.nilradical_eq_iInf]
  apply le_antisymm
  · exact iInf_le_of_le
      (⟨IsLocalRing.maximalIdeal R, IsLocalRing.maximalIdeal.isMaximal R⟩ : MaximalSpectrum R)
      le_rfl
  · apply le_iInf
    intro p
    exact le_of_eq (IsLocalRing.eq_maximalIdeal p.isMaximal).symm

theorem artinian_local_isAdicComplete [IsArtinianRing R] [IsLocalRing R] :
    IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
  rw [← artinian_local_nilradical_eq_maximalIdeal]
  exact isAdicComplete_of_nilpotent_ideal (nilradical R) R
    IsArtinianRing.isNilpotent_nilradical

def artinianLocalCompletionEquiv [IsArtinianRing R] [IsLocalRing R] :
    R ≃ₐ[R] AdicCompletion (IsLocalRing.maximalIdeal R) R := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) R := artinian_local_isAdicComplete
  exact AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal R)

theorem artinian_local_socle_generator_of_completion [IsArtinianRing R] [IsLocalRing R]
    (theta : R)
    (h : (nilradical (AdicCompletion (IsLocalRing.maximalIdeal R) R)).annihilator =
      Ideal.span {AdicCompletion.of (IsLocalRing.maximalIdeal R) R theta}) :
    (nilradical R).annihilator = Ideal.span {theta} := by
  let S := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let e : R ≃ₐ[R] S := artinianLocalCompletionEquiv
  let : IsLocalRing S := e.toRingEquiv.isLocalRing
  let : IsArtinianRing S := e.toRingEquiv.isArtinianRing
  change (nilradical S).annihilator = Ideal.span {e theta} at h
  rw [artinian_local_nilradical_eq_maximalIdeal] at h ⊢
  ext x
  rw [ringEquiv_socle_iff e.toRingEquiv x, h]
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.symm b, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply]
    exact hb
  · intro hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e b, ?_⟩
    rw [hb, map_mul]
    rfl

end LinearStudy
