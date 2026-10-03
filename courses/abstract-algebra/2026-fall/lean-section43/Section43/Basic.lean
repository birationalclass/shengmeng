module

public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Order.WellFounded

/-!
# Abstract algebra, Section 4.3: unique factorization domains

Source: `lesson-groups/sections/4.3.json` in birationalclass/shengmeng.
The theorem numbers below are those in the course, not the negativity project.
`IsRelPrime` expresses that common divisors are units; it does not assert Bézout.
-/

@[expose] public section

namespace Section43

set_option autoImplicit false

variable {R : Type*} [CommRing R] [hDomain : IsDomain R]
include hDomain

/-- Definition 4.3.1. -/
theorem divides_iff (a b : R) : b ∣ a ↔ ∃ c, a = b * c := Iff.rfl

/-- Theorem 4.3.1: transitivity. -/
theorem divides_trans {a b c : R} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c :=
  hab.trans hbc

/-- Theorem 4.3.1: a common divisor divides every linear combination. -/
theorem divides_linear_combination {d a b : R} (ha : d ∣ a) (hb : d ∣ b) (x y : R) :
    d ∣ x * a + y * b :=
  (dvd_mul_of_dvd_right ha x).add (dvd_mul_of_dvd_right hb y)

/-- Theorem 4.3.2: association is mutual divisibility. -/
theorem associated_iff_mutual_divisibility (a b : R) :
    Associated a b ↔ a ∣ b ∧ b ∣ a := dvd_dvd_iff_associated.symm

/-- Theorem 4.3.2: equality of principal ideals. -/
theorem principal_ideals_eq_iff (a b : R) :
    Ideal.span ({a} : Set R) = Ideal.span ({b} : Set R) ↔ Associated a b :=
  Ideal.span_singleton_eq_span_singleton

/-- Theorem 4.3.2: associated elements differ by a unit. -/
theorem associated_iff_unit_multiple (a b : R) :
    Associated a b ↔ ∃ u : Rˣ, b = a * u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu.symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu.symm⟩

theorem association_equivalence : Equivalence (@Associated R _) :=
  ⟨Associated.refl, Associated.symm, Associated.trans⟩

/-- Theorem 4.3.3 holds in every integral domain. -/
theorem prime_is_irreducible {p : R} (hp : Prime p) : Irreducible p := hp.irreducible

section Factorization

variable [UniqueFactorizationMonoid R]

/-- Definition 4.3.6: existence of factorization, including units via the empty multiset. -/
theorem factorization_exists (a : R) (ha : a ≠ 0) :
    ∃ f : Multiset R, (∀ p ∈ f, Irreducible p) ∧ Associated f.prod a :=
  WfDvdMonoid.exists_factors a ha

/-- Definition 4.3.6: uniqueness up to permutation and association of individual factors. -/
theorem factorization_unique {f g : Multiset R}
    (hf : ∀ p ∈ f, Irreducible p) (hg : ∀ p ∈ g, Irreducible p)
    (h : Associated f.prod g.prod) : Multiset.Rel Associated f g :=
  UniqueFactorizationMonoid.factors_unique hf hg h

/-- Theorem 4.3.5. -/
theorem irreducible_iff_prime (p : R) : Irreducible p ↔ Prime p :=
  UniqueFactorizationMonoid.irreducible_iff_prime

open scoped Classical in
/-- Definition 4.3.7: the normalized power-product representation, up to a unit. -/
theorem normalized_power_factorization [NormalizationMonoid R] (a : R) (ha : a ≠ 0) :
    Associated (∏ᶠ p : R, p ^ (UniqueFactorizationMonoid.normalizedFactors a).count p) a :=
  UniqueFactorizationMonoid.associated_finprod_pow_count ha

/-- Definition 4.3.7 in the course's finite form: a unit, positive exponents, and
pairwise nonassociate irreducibles. No normalization structure is an extra hypothesis. -/
theorem standard_factorization_exists (a : R) (ha : a ≠ 0) :
    ∃ (s : Finset R) (e : R → ℕ) (u : Rˣ),
      a = u * ∏ p ∈ s, p ^ e p ∧
      (∀ p ∈ s, Irreducible p ∧ 0 < e p) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → ¬ Associated p q) := by
  classical
  let _ : NormalizationMonoid R := Classical.arbitrary _
  let f := UniqueFactorizationMonoid.normalizedFactors a
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors ha
  refine ⟨f.toFinset, fun p ↦ f.count p, u, ?_, ?_, ?_⟩
  · rw [← Finset.prod_multiset_count]
    exact (mul_comm (u : R) f.prod).trans hu |>.symm
  · intro p hp
    have hp' : p ∈ f := Multiset.mem_toFinset.mp hp
    exact ⟨UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp',
      Multiset.count_pos.mpr hp'⟩
  · intro p hp q hq hpq hassoc
    apply hpq
    exact hassoc.eq_of_normalized
      (UniqueFactorizationMonoid.normalize_normalized_factor p (Multiset.mem_toFinset.mp hp))
      (UniqueFactorizationMonoid.normalize_normalized_factor q (Multiset.mem_toFinset.mp hq))

/-- Theorem 4.3.6: strict divisibility is well-founded. -/
theorem strict_divisibility_wellFounded : WellFounded (@DvdNotUnit R _) :=
  wellFounded_dvdNotUnit

/-- Theorem 4.3.6, expressed literally as the absence of infinite descending chains. -/
theorem no_infinite_proper_divisor_chain :
    ¬ ∃ f : ℕ → R, ∀ n, DvdNotUnit (f (n + 1)) (f n) := by
  rintro ⟨f, hf⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp
    (strict_divisibility_wellFounded (R := R))).false ⟨f, hf⟩

end Factorization

/-- Theorem 4.3.7: well-founded strict divisibility plus prime irreducibles imply UFD. -/
theorem ufd_of_chain_condition_and_prime_irreducibles
    (hwf : WellFounded (@DvdNotUnit R _))
    (hp : ∀ p : R, Irreducible p → Prime p) : UniqueFactorizationMonoid R := by
  exact { toWellFounded := hwf, irreducible_iff_prime := ⟨hp _, Prime.irreducible⟩ }

/-- Theorem 4.3.7: the full equivalence. -/
theorem ufd_iff_chain_condition_and_prime_irreducibles :
    UniqueFactorizationMonoid R ↔
      WellFounded (@DvdNotUnit R _) ∧ (∀ p : R, Irreducible p → Prime p) := by
  constructor
  · intro h
    let := h
    exact ⟨strict_divisibility_wellFounded, fun p ↦ (irreducible_iff_prime p).mp⟩
  · rintro ⟨hwf, hp⟩
    exact ufd_of_chain_condition_and_prime_irreducibles hwf hp

/-- Theorems 4.3.6–4.3.7 using the course's infinite-chain language. -/
theorem ufd_iff_no_infinite_chain_and_prime_irreducibles :
    UniqueFactorizationMonoid R ↔
      (¬ ∃ f : ℕ → R, ∀ n, DvdNotUnit (f (n + 1)) (f n)) ∧
      (∀ p : R, Irreducible p → Prime p) := by
  rw [ufd_iff_chain_condition_and_prime_irreducibles,
    wellFounded_iff_isEmpty_descending_chain]
  simp only [isEmpty_iff, Subtype.forall, not_exists]

/-- The course's multiset definition agrees with mathlib's UFD typeclass. -/
theorem ufd_iff_unique_factorization :
    UniqueFactorizationMonoid R ↔
      (∀ a : R, a ≠ 0 → ∃ f : Multiset R,
        (∀ p ∈ f, Irreducible p) ∧ Associated f.prod a) ∧
      (∀ f g : Multiset R, (∀ p ∈ f, Irreducible p) →
        (∀ p ∈ g, Irreducible p) →
        Associated f.prod g.prod → Multiset.Rel Associated f g) := by
  constructor
  · intro h
    let := h
    exact ⟨factorization_exists, fun _ _ ↦ factorization_unique⟩
  · rintro ⟨hex, huniq⟩
    exact UniqueFactorizationMonoid.of_existsUnique_irreducible_factors hex huniq

/-- Definition 4.3.9, without choosing a representative. -/
def IsGreatestCommonDivisor (d a b : R) : Prop :=
  d ∣ a ∧ d ∣ b ∧ ∀ c : R, c ∣ a → c ∣ b → c ∣ d

section GCD

variable [UniqueFactorizationMonoid R]
noncomputable local instance : GCDMonoid R := UniqueFactorizationMonoid.toGCDMonoid R

/-- Theorem 4.3.8: existence, including zero arguments. -/
theorem gcd_exists (a b : R) : ∃ d, IsGreatestCommonDivisor d a b :=
  ⟨gcd a b, gcd_dvd_left a b, gcd_dvd_right a b, fun _ ↦ dvd_gcd⟩

/-- Theorem 4.3.8: exponents in a gcd are minima (with infinity allowed at zero). -/
theorem gcd_prime_exponent (p a b : R) :
    emultiplicity p (gcd a b) = min (emultiplicity p a) (emultiplicity p b) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [← pow_dvd_iff_le_emultiplicity, le_min_iff,
    ← pow_dvd_iff_le_emultiplicity, ← pow_dvd_iff_le_emultiplicity]
  exact dvd_gcd_iff (a := p ^ n) (b := a) (c := b)

theorem gcd_zero (a : R) : Associated (gcd 0 a) a := gcd_zero_left' a

omit [UniqueFactorizationMonoid R] in
/-- Theorem 4.3.8: uniqueness up to association. -/
theorem gcd_unique_up_to_association {d e a b : R}
    (hd : IsGreatestCommonDivisor d a b) (he : IsGreatestCommonDivisor e a b) :
    Associated d e :=
  associated_of_dvd_dvd (he.2.2 d hd.1 hd.2.1) (hd.2.2 e he.1 he.2.1)

/-- Definition 4.3.10: a gcd is a unit iff all common divisors are units. -/
theorem relatively_prime_iff_unit_gcd (a b : R) :
    IsRelPrime a b ↔ IsUnit (gcd a b) := gcd_isUnit_iff_isRelPrime.symm

/-- Theorem 4.3.9(1): Euclid's lemma for relatively prime elements. -/
theorem relatively_prime_divides_product {a b c : R}
    (h : IsRelPrime a b) (hd : a ∣ b * c) : a ∣ c :=
  h.dvd_of_dvd_mul_left hd

/-- Theorem 4.3.9(2): relatively prime divisors have a product dividing the target. -/
theorem relatively_prime_product_divides {a b c : R}
    (h : IsRelPrime a b) (ha : a ∣ c) (hb : b ∣ c) : a * b ∣ c := h.mul_dvd ha hb

/-- Theorem 4.3.9(3): the gcd product formula, with the required association. -/
theorem relatively_prime_gcd_product {a b c : R} (h : IsRelPrime a b) :
    Associated (gcd a c * gcd b c) (gcd (a * b) c) := by
  apply associated_of_dvd_dvd
  · have h' : IsRelPrime (gcd a c) (gcd b c) :=
      fun _ hd he ↦ h (hd.trans (gcd_dvd_left a c)) (he.trans (gcd_dvd_left b c))
    exact dvd_gcd (mul_dvd_mul (gcd_dvd_left a c) (gcd_dvd_left b c))
      (h'.mul_dvd (gcd_dvd_right a c) (gcd_dvd_right b c))
  · exact (gcd_comm' (a * b) c).dvd.trans
      ((gcd_mul_dvd_mul_gcd c a b).trans
        (((gcd_comm' c a).mul_mul (gcd_comm' c b)).dvd))

end GCD

end Section43
