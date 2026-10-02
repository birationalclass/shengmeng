module

public import Negativity.InfinityNorm
public import Negativity.FractionFieldOrders
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain IsDiscreteValuationRing
set_option backward.isDefEq.respectTransparency false

/-- The adic multiplicity of a regular equation in a genuine DVR is
exactly its normalized additive DVR order. -/
theorem dvr_heightOneOrder_regular (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (r : R) (hr : r ≠ 0) :
    heightOneOrder K (IsDiscreteValuationRing.maximalIdeal R)
      (Units.mk0 (algebraMap R K r)
        (by simpa only [map_zero] using (IsFractionRing.injective R K).ne hr)) =
      ((addVal R r).toNat : ℤ) := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  obtain ⟨n, u, he⟩ := eq_unit_mul_pow_irreducible hr hπ
  rw [heightOneOrder_regular_eq_multiplicity R K _ r hr,
    addVal_def r u hπ n he, ENat.toNat_natCast]
  have hi : Ideal.span {r} = (IsLocalRing.maximalIdeal R) ^ n := by
    rw [he, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
  rw [hi]
  exact congrArg (fun t : ℕ ↦ (t : ℤ))
    (multiplicity_pow_self_of_prime
      (IsDiscreteValuationRing.maximalIdeal R).irreducible.prime n)

/-- The two actual definitions of rational order agree, including poles:
adic valuation on the fraction field and signed numerator/denominator DVR order. -/
theorem dvr_heightOneOrder_eq_rationalOrder (R K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) :
    heightOneOrder K (IsDiscreteValuationRing.maximalIdeal R) a =
      DvrRationalOrder R K a := by
  obtain ⟨⟨r, s⟩, he⟩ := IsLocalization.surj (nonZeroDivisors R) (a : K)
  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hsk : algebraMap R K (s : R) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hs
  have hr : r ≠ 0 := by
    intro hz
    exact mul_ne_zero a.ne_zero hsk (by simpa only [hz, map_zero] using he)
  have hrk : algebraMap R K r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hr
  have ha : (a : K) = algebraMap R K r / algebraMap R K (s : R) :=
    (eq_div_iff hsk).mpr he
  let p := IsDiscreteValuationRing.maximalIdeal R
  have hvr : p.valuation K (algebraMap R K r) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hrk
  have hvs : p.valuation K (algebraMap R K (s : R)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hsk
  have hro := dvr_heightOneOrder_regular R K r hr
  have hso := dvr_heightOneOrder_regular R K (s : R) hs
  rw [dvr_rationalOrder_represents R K a r s hr hs he]
  unfold heightOneOrder at hro hso ⊢
  rw [ha, map_div₀, WithZero.log_div hvr hvs]
  change _ = ((addVal R r).toNat : ℤ) - ((addVal R (s : R)).toNat : ℤ)
  change -WithZero.log (p.valuation K (algebraMap R K r)) = _ at hro
  change -WithZero.log (p.valuation K (algebraMap R K (s : R))) = _ at hso
  omega

/-- Final theorem: the order at an actual Dedekind chart prime is the
signed DVR order in its actual adic valuation ring. The normalizations
agree because a genuine uniformizer has value exp(-1), not just because
the two valuations define the same subring. -/
theorem dedekind_prime_order_eq_valuationRing_order
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : HeightOneSpectrum R) (a : Kˣ) :
    heightOneOrder K p a = DvrRationalOrder (p.valuation K).valuationSubring K a := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  have hv := normalized_discrete_valuation_eq K (p.valuation K) π hπ
  rw [← dvr_heightOneOrder_eq_rationalOrder]
  unfold heightOneOrder
  rw [hv]

end Negativity
