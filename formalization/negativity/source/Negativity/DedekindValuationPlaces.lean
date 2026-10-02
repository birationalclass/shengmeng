module

public import Negativity.ValuationCenters
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain
set_option backward.isDefEq.respectTransparency false

/-- Inverting an actual regular unit keeps a fraction inside the actual
valuation subring. Used to extend the chart through prime-complement
denominators, rather than assuming a local-chart identification. -/
theorem valuation_fraction_mem_of_unit_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (A : ValuationSubring K) (hR : ∀ r : R, algebraMap R K r ∈ A)
    (r d : R)
    (hu : IsUnit (((algebraMap R K).codRestrict A.toSubring hR) d)) :
    algebraMap R K r * (algebraMap R K d)⁻¹ ∈ A := by
  have hd : A.valuation (algebraMap R K d) = 1 :=
    (A.valuation_eq_one_iff _).mp hu
  have hi : (algebraMap R K d)⁻¹ ∈ A := by
    rw [← A.valuation_le_one_iff, map_inv₀, hd, inv_one]
  exact A.toSubring.mul_mem (hR r) hi

/-- A nontrivial valuation of the fraction field containing an actual
domain has a nonzero center prime on that domain. If the center were zero,
all nonzero denominators would be units and the valuation ring would be K. -/
theorem valuation_chart_center_nonzero
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (A : ValuationSubring K) (hA : A ≠ ⊤)
    (hR : ∀ r : R, algebraMap R K r ∈ A) :
    (IsLocalRing.maximalIdeal A).comap
      ((algebraMap R K).codRestrict A.toSubring hR) ≠ ⊥ := by
  let f := (algebraMap R K).codRestrict A.toSubring hR
  intro hp
  apply hA
  apply top_unique
  intro a _
  obtain ⟨⟨r, d⟩, he⟩ := IsLocalization.surj (nonZeroDivisors R) a
  have hd : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hdk : algebraMap R K (d : R) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hd
  have hu : IsUnit (f d) := by
    by_contra h
    have hm : (d : R) ∈ (IsLocalRing.maximalIdeal A).comap f := h
    rw [hp, Ideal.mem_bot] at hm
    exact hd hm
  have ha : a = algebraMap R K r * (algebraMap R K (d : R))⁻¹ := by
    rw [← div_eq_mul_inv, eq_div_iff hdk]
    exact he
  rw [ha]
  exact valuation_fraction_mem_of_unit_denominator A hR r d hu

/-- Final theorem: a nontrivial actual valuation ring containing a
Dedekind chart is exactly the normalized adic valuation ring of a unique
actual height-one prime of that chart. The center prime and localization
are constructed; no prime/valuation correspondence is supplied. -/
theorem dedekind_chart_valuation_unique_prime
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (A : ValuationSubring K) (hA : A ≠ ⊤)
    (hR : ∀ r : R, algebraMap R K r ∈ A) :
    ∃! p : HeightOneSpectrum R, (p.valuation K).valuationSubring = A := by
  let f := (algebraMap R K).codRestrict A.toSubring hR
  let p : HeightOneSpectrum R := {
    asIdeal := (IsLocalRing.maximalIdeal A).comap f,
    isPrime := Ideal.comap_isPrime f _,
    ne_bot := valuation_chart_center_nonzero R K A hA hR }
  have hle : p.valuationSubringAtPrime K ≤ A := by
    rintro a ⟨r, d, hd, rfl⟩
    have hu : IsUnit (f d) := by
      by_contra h
      exact hd (show d ∈ p.asIdeal from h)
    exact valuation_fraction_mem_of_unit_denominator A hR r d hu
  have he : p.valuationSubringAtPrime K = A :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hA
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at he
  exact ⟨p, he, fun q hq ↦
    HeightOneSpectrum.valuationSubring_valuation_injective K (hq.trans he.symm)⟩

end Negativity
