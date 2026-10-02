/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0; the project includes THIRD_PARTY_NOTICES.txt.
Original author: Andrew Yang. Adapted for the Negativity formalization.
The determinant-trick argument below adapts Andrew Yang's
maximalIdeal_isPrincipal_of_isDedekindDomain in mathlib (Apache 2.0).
The input here is an annihilator witness, without a Dedekind hypothesis.
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsLocalRing

/-- In a normal Noetherian local domain, an annihilator witness for a
nonzero principal quotient forces the maximal ideal to be principal.
This is the local algebra behind height-one extension, rather than
an assumed codimension-one intersection statement. -/
theorem normal_local_annihilator_maximal_isPrincipal (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a b : R) (ha : a ≠ 0)
    (hb : b ∉ Ideal.span {a})
    (hm : ∀ m ∈ maximalIdeal R, ∃ k : R, k * a = b * m) :
    (maximalIdeal R).IsPrincipal := by
  classical
  have haunit : ¬ IsUnit a := by
    intro h
    apply hb
    rw [Ideal.span_singleton_eq_top.mpr h]
    trivial
  have ham : a ∈ maximalIdeal R := by
    simpa only [mem_maximalIdeal, mem_nonunits_iff] using haunit
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (Ideal.zero_mem _)
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have hak : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  by_cases hx : ∀ y ∈ M, x * y ∈ M
  · have hi := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      refine (hb (Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, hy, div_mul_cancel₀ _ hak]
    · rw [Submodule.ne_bot_iff]
      exact ⟨_, ⟨a, ham, rfl⟩, hak⟩
    · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
  · have htop :
        (M.map (DistribSMul.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      contrapose! hx with h
      rintro m' ⟨m, hm', rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hm m hm'
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel_right₀ _ hak]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm', rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hym, hy⟩ : ∃ y ∈ maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at htop
      obtain ⟨_, ⟨y, hym, rfl⟩, hy : x * algebraMap R K y = algebraMap R K 1⟩ := htop
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq hak, ← map_mul] at hy
      exact ⟨y, hym, IsFractionRing.injective R K hy⟩
    refine ⟨⟨y, ?_⟩⟩
    apply le_antisymm
    · intro m hm'
      obtain ⟨k, hk⟩ := hm m hm'
      rw [← hy, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb0 hk, mul_comm]
      exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

/-- An actual associated maximal prime of a nonzero principal quotient
provides the annihilator witness, so its principality is a theorem. -/
theorem normal_local_associated_principal_maximal_isPrincipal (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : R) (ha : a ≠ 0)
    (h : IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.span {a})) :
    (maximalIdeal R).IsPrincipal := by
  classical
  obtain ⟨_, v, hv⟩ := isAssociatedPrime_iff.mp h
  have hv0 : v ≠ 0 := by
    rintro rfl
    have ht : maximalIdeal R = ⊤ := by
      simpa only [Submodule.colon_singleton_zero] using hv
    exact (maximalIdeal.isMaximal R).ne_top ht
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
  apply normal_local_annihilator_maximal_isPrincipal R a b ha
  · exact fun hb => hv0 (Ideal.Quotient.eq_zero_iff_mem.mpr hb)
  · intro m hm
    rw [hv, Submodule.mem_colon_singleton, Submodule.mem_bot] at hm
    have hm' : m * b ∈ Ideal.span {a} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] using hm
    simpa only [mul_comm] using Ideal.mem_span_singleton'.mp hm'

/-- The same associated-prime witness forces an actual DVR, without an
input dimension bound. This will detect height-one primes after
localizing the principal quotient at an associated prime. -/
theorem normal_local_associated_principal_isDVR (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] (a : R) (ha : a ≠ 0)
    (h : IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.span {a})) :
    IsDiscreteValuationRing R := by
  have hp := normal_local_associated_principal_maximal_isPrincipal R a ha h
  have hf : ¬ IsField R := by
    intro hf
    let := hf.toField
    have he : Ideal.span {a} = ⊤ := Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr ha)
    rw [he] at h
    exact not_isAssociatedPrime_of_subsingleton h
  exact ((IsDiscreteValuationRing.TFAE R hf).out 5 1).mp hp

/-- Localizing a genuine associated prime of a nonzero principal
quotient gives a DVR in a normal Noetherian domain. -/
theorem normal_principal_associated_prime_isDVR (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (a : R) (ha : a ≠ 0) (p : Ideal R) [p.IsPrime]
    (hp : IsAssociatedPrime p (R ⧸ Ideal.span {a})) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  classical
  let S := Localization.AtPrime p
  haveI : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S p.primeCompl p.primeCompl_le_nonZeroDivisors
  obtain ⟨_, v, hv⟩ := isAssociatedPrime_iff.mp hp
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hp.isPrime.ne_top (by simpa only [Submodule.colon_singleton_zero] using hv)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hab : algebraMap R S a ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap R S)
      (IsLocalization.injective S p.primeCompl_le_nonZeroDivisors)).mpr ha
  have hbS : algebraMap R S b ∉ Ideal.span {algebraMap R S a} := by
    intro hbS
    have he : (Ideal.span {a}).map (algebraMap R S) =
        Ideal.span {algebraMap R S a} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← he, IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl] at hbS
    obtain ⟨s, hs, hsb⟩ := hbS
    apply hs
    change s ∈ p
    rw [hv, Submodule.mem_colon_singleton, Submodule.mem_bot]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr at hsb
    simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] using hsb
  have hm : ∀ m ∈ maximalIdeal S, ∃ k : S,
      k * algebraMap R S a = algebraMap R S b * m := by
    intro m hm
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl m
    have hr : r ∈ p := by
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p r).mp
        (IsLocalization.mk'_mem_iff.mp hm)
    rw [hv, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
    have hrb : r * b ∈ Ideal.span {a} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] using hr
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hrb
    refine ⟨IsLocalization.mk' S k s, ?_⟩
    calc
      IsLocalization.mk' S k s * algebraMap R S a =
          IsLocalization.mk' S (k * a) (s * 1) := by
        rw [IsLocalization.mk'_mul, IsLocalization.mk'_one]
      _ = IsLocalization.mk' S (b * r) (1 * s) := by rw [hk, mul_comm r b, mul_one, one_mul]
      _ = algebraMap R S b * IsLocalization.mk' S r s := by
        rw [IsLocalization.mk'_mul, IsLocalization.mk'_one]
  have hprin := normal_local_annihilator_maximal_isPrincipal S _ _ hab hbS hm
  have hf : ¬ IsField S := by
    intro hf
    let := hf.toField
    have he : Ideal.span {algebraMap R S a} = ⊤ :=
      Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr hab)
    exact hbS (he ▸ trivial)
  exact ((IsDiscreteValuationRing.TFAE S hf).out 5 1).mp hprin

/-- Associated primes of a nonzero principal quotient in a normal
Noetherian domain have height exactly one. -/
theorem normal_principal_associated_prime_height_one (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (a : R) (ha : a ≠ 0) (p : Ideal R) [p.IsPrime]
    (hp : IsAssociatedPrime p (R ⧸ Ideal.span {a})) : p.height = 1 := by
  haveI := normal_principal_associated_prime_isDVR R a ha p hp
  apply WithBot.coe_injective
  change (p.height : WithBot ℕ∞) = 1
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  exact IsDiscreteValuationRing.ringKrullDim_eq_one (Localization.AtPrime p)

/-- Divisibility in a normal Noetherian domain is detected at its
height-one localizations. No codimension-one extension hypothesis
is assumed: the preceding associated-prime theorem proves it. -/
theorem normal_divisibility_of_height_one_local (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (a b : R) (ha : a ≠ 0)
    (hloc : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R (Localization.AtPrime p) b ∈
        Ideal.span {algebraMap R (Localization.AtPrime p) a}) :
    b ∈ Ideal.span {a} := by
  classical
  by_contra hb
  have hv : Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0 := by
    exact fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hv
  haveI := hp.isPrime
  have ht := normal_principal_associated_prime_height_one R a ha p hp
  have hm := hloc p ht
  have he : (Ideal.span {a}).map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span {algebraMap R (Localization.AtPrime p) a} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [← he, IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl] at hm
  obtain ⟨s, hs, hsb⟩ := hm
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr at hsb
  simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] using hsb

/-- A rational function on a normal Noetherian affine scheme is regular
if it is regular at every height-one point. This is the actual
fraction-field intersection theorem, including arbitrary characteristic. -/
theorem normal_fraction_regular_iff_height_one (R : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (x : FractionRing R) :
    (∃ r : R, algebraMap R (FractionRing R) r = x) ↔
    ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ y : Localization.AtPrime p,
        algebraMap (Localization.AtPrime p) (FractionRing R) y = x := by
  classical
  constructor
  · rintro ⟨r, rfl⟩ p _ _
    exact ⟨algebraMap R (Localization.AtPrime p) r,
      (IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (FractionRing R) r).symm⟩
  · intro hloc
    obtain ⟨b, a, ha, rfl⟩ := IsFractionRing.div_surjective R x
    have han : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hak : algebraMap R (FractionRing R) a ≠ 0 :=
      IsFractionRing.to_map_eq_zero_iff.not.mpr han
    have hb : b ∈ Ideal.span {a} := by
      apply normal_divisibility_of_height_one_local R a b han
      intro p _ hp
      obtain ⟨y, hy⟩ := hloc p hp
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨y, ?_⟩
      apply IsFractionRing.injective (Localization.AtPrime p) (FractionRing R)
      rw [map_mul, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime p),
        ← IsScalarTower.algebraMap_apply R (Localization.AtPrime p), hy,
        div_mul_cancel₀ _ hak]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨r, ?_⟩
    rw [eq_div_iff hak, ← map_mul, hr]

/-- The height-one extension criterion in any fraction field, expressed
by actual denominators outside each height-one prime. This form can be
applied directly to local equations in scheme stalks. -/
theorem normal_fraction_regular_of_height_one_denominators (R K : Type*)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K)
    (hloc : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ (r s : R), s ∉ p ∧ x * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, algebraMap R K r = x := by
  classical
  obtain ⟨b, a, ha, rfl⟩ := IsFractionRing.div_surjective R x
  have han : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hak : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr han
  have hb : b ∈ Ideal.span {a} := by
    apply normal_divisibility_of_height_one_local R a b han
    intro p _ hp
    obtain ⟨r, s, hs, heq⟩ := hloc p hp
    have hsb : s * b = r * a := by
      apply IsFractionRing.injective R K
      rw [map_mul, map_mul]
      have he := congrArg (fun z : K => z * algebraMap R K a) heq
      rw [← mul_div_right_comm, div_mul_cancel₀ _ hak] at he
      simpa only [mul_comm] using he
    have he' : (Ideal.span {a}).map (algebraMap R (Localization.AtPrime p)) =
        Ideal.span {algebraMap R (Localization.AtPrime p) a} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← he', IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
    exact ⟨s, hs, Ideal.mem_span_singleton'.mpr ⟨r, hsb.symm⟩⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨r, ?_⟩
  rw [eq_div_iff hak, ← map_mul, hr]

end Negativity
