module

public import Linear.KoszulSocleDeterminant
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsNoetherianRing A]

theorem artinian_maximal_annihilator_nonzero (I : Ideal A) (hI : I.IsMaximal) :
    I.annihilator ≠ ⊥ := by
  let : I.IsPrime := hI.isPrime
  have hmin : I ∈ (Module.annihilator A A).minimalPrimes := by
    rw [Module.annihilator_eq_bot.mpr inferInstance]
    exact IsArtinianRing.mem_minimalPrimes bot_le
  have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A A hmin
  obtain ⟨_, x, hx⟩ := isAssociatedPrime_iff.mp hass
  have hx0 : x ≠ 0 := by
    intro hx0
    apply hI.ne_top
    apply (Ideal.eq_top_iff_one I).mpr
    rw [hx, Submodule.mem_colon_singleton]
    simp [hx0]
  have hxann : x ∈ I.annihilator := by
    apply Submodule.mem_annihilator.mpr
    intro a ha
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
    simpa [smul_eq_mul, mul_comm] using ha
  intro hz
  rw [hz] at hxann
  exact hx0 hxann

theorem nonzero_ideal_meets_maximal_annihilator (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ p : MaximalSpectrum A, ∃ x : A,
      x ∈ I ∧ x ≠ 0 ∧ x ∈ p.asIdeal.annihilator := by
  let : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty A I
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hp
  let : p.IsPrime := hpp
  let pm : MaximalSpectrum A := ⟨p, IsArtinianRing.isMaximal_of_isPrime p⟩
  have hx0 : (x : A) ≠ 0 := by
    intro hx0
    have hzero : x = 0 := Subtype.ext hx0
    apply hpp.ne_top
    apply (Ideal.eq_top_iff_one p).mpr
    rw [hx, Submodule.mem_colon_singleton]
    simp [hzero]
  refine ⟨pm, x, x.property, hx0, ?_⟩
  apply Submodule.mem_annihilator.mpr
  intro a ha
  change a ∈ p at ha
  rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot] at ha
  have he := congrArg Subtype.val ha
  simpa [smul_eq_mul, mul_comm] using he

theorem coefficientDeterminant_ne_zero_of_artinian_maximal
    {R : Type*} [CommRing R] {k : ℕ} (H x : Fin (k + 1) → R)
    (hH : RingTheory.Sequence.IsRegular R (List.ofFn H))
    (hx : RingTheory.Sequence.IsRegular R (List.ofFn x))
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (h : M.mulVec x = H)
    [IsArtinianRing (R ⧸ Ideal.span (Set.range H))]
    [IsNoetherianRing (R ⧸ Ideal.span (Set.range H))]
    (hm : ((Ideal.span (Set.range x)).map
      (Ideal.Quotient.mk (Ideal.span (Set.range H)))).IsMaximal) :
    Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det ≠ 0 := by
  have he := coordinate_annihilator_eq_coefficientDeterminant H x hH hx M h
  have hn := artinian_maximal_annihilator_nonzero _ hm
  rw [he] at hn
  intro hd
  exact hn (by simp [hd])

variable {K : Type*} [Field K] [Algebra K A]

theorem global_socle_functional_detects_nonzero
    (delta : MaximalSpectrum A → A)
    (hsoc : ∀ p, ∀ x : A, x ∈ p.asIdeal.annihilator → ∃ b : K, x = b • delta p)
    (ell : A →ₗ[K] K) (hell : ∀ p, ell (delta p) ≠ 0)
    {x : A} (hx : x ≠ 0) : ∃ a : A, ell (x * a) ≠ 0 := by
  have hI : Ideal.span ({x} : Set A) ≠ ⊥ := by
    intro h
    have hm := Ideal.subset_span (Set.mem_singleton x)
    rw [h] at hm
    exact hx hm
  obtain ⟨p, y, hy, hy0, hys⟩ := nonzero_ideal_meets_maximal_annihilator _ hI
  obtain ⟨b, hb⟩ := hsoc p y hys
  have hb0 : b ≠ 0 := by
    intro h
    exact hy0 (by simpa [h] using hb)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨a, ?_⟩
  have hell_y : ell y ≠ 0 := by
    rw [hb, map_smul, smul_eq_mul]
    exact mul_ne_zero hb0 (hell p)
  simpa [ha] using hell_y

theorem global_socle_multiplicationToDual_injective
    (delta : MaximalSpectrum A → A)
    (hsoc : ∀ p, ∀ x : A, x ∈ p.asIdeal.annihilator → ∃ b : K, x = b • delta p)
    (ell : A →ₗ[K] K) (hell : ∀ p, ell (delta p) ≠ 0) :
    Function.Injective (multiplicationToDual ell) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hx0
  obtain ⟨a, ha⟩ := global_socle_functional_detects_nonzero delta hsoc ell hell hx0
  exact ha (congrArg (fun f : A →ₗ[K] K => f a) hx)

def perfectPairingOfGlobalSocles [FiniteDimensional K A]
    (delta : MaximalSpectrum A → A)
    (hsoc : ∀ p, ∀ x : A, x ∈ p.asIdeal.annihilator → ∃ b : K, x = b • delta p)
    (ell : A →ₗ[K] K) (hell : ∀ p, ell (delta p) ≠ 0) :
    PerfectMultiplicationPairing (B := K) (A := A) where
  functional := ell
  equiv := LinearEquiv.ofInjectiveOfFinrankEq (multiplicationToDual ell)
    (global_socle_multiplicationToDual_injective delta hsoc ell hell)
    Subspace.dual_finrank_eq.symm
  equiv_apply := by intro x a; rfl

theorem exists_perfectPairing_of_global_scalar_socles [Infinite K] [FiniteDimensional K A]
    (delta : MaximalSpectrum A → A) (hdelta : ∀ p, delta p ≠ 0)
    (hsoc : ∀ p, ∀ x : A, x ∈ p.asIdeal.annihilator → ∃ b : K, x = b • delta p) :
    ∃ p : PerfectMultiplicationPairing (B := K) (A := A),
      ∀ j, p.functional (delta j) ≠ 0 := by
  obtain ⟨ell, hell⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) delta hdelta
  exact ⟨perfectPairingOfGlobalSocles delta hsoc ell hell, hell⟩

end LinearStudy
