module

public import Negativity.CurveDegree
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain

/-- A nonzero rational function has only finitely many nonzero orders on an
actual affine Dedekind curve. Finiteness is proved, not supplied as an input. -/
theorem heightOneOrder_finite_support {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (a : Kˣ) :
    (Function.support (fun p : HeightOneSpectrum R => heightOneOrder K p a)).Finite := by
  have hfin := (HeightOneSpectrum.Support.finite (R := R) (a : K)).union
    (HeightOneSpectrum.Support.finite (R := R) (a : K)⁻¹)
  apply hfin.subset
  intro p hp
  have hone : p.valuation K (a : K) ≠ 1 := by
    intro h
    simp [Function.mem_support, heightOneOrder, h] at hp
  rcases lt_or_gt_of_ne hone with hlt | hgt
  · right
    change 1 < p.valuation K ((a : K)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (WithZero.pos_iff_ne_zero.mpr
      ((Valuation.ne_zero_iff _).mpr a.ne_zero))).mpr hlt
  · exact Or.inl hgt

/-- The genuine principal Weil divisor on an affine Dedekind curve, with
coefficients supplied by actual normalized valuations. -/
noncomputable def affinePrincipalDivisor {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (a : Kˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p : HeightOneSpectrum R => heightOneOrder K p a)
    (heightOneOrder_finite_support (R := R) K a)

/-- Coefficients of this divisor are the actual local orders. -/
theorem affinePrincipalDivisor_apply {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) (p : HeightOneSpectrum R) :
    affinePrincipalDivisor K a p = heightOneOrder K p a := rfl

/-- Principal Weil divisors add under multiplication of rational functions. -/
theorem affinePrincipalDivisor_mul {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (a b : Kˣ) :
    affinePrincipalDivisor (R := R) K (a * b) =
      affinePrincipalDivisor K a + affinePrincipalDivisor K b := by
  ext p
  exact heightOneOrder_mul K p a b

/-- A unit of the affine coordinate ring has order zero at every point. -/
theorem heightOneOrder_regular_unit {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) (u : Rˣ) :
    heightOneOrder K p (Units.map (algebraMap R K : R →* K) u) = 0 := by
  have hunit : p.intValuation (u : R) = 1 := by
    apply le_antisymm (p.intValuation_le_one _)
    calc
      1 = p.intValuation (u : R) * p.intValuation ((u⁻¹ : Rˣ) : R) := by
        rw [← map_mul]; simp
      _ ≤ p.intValuation (u : R) * 1 :=
        mul_le_mul_of_nonneg_left (p.intValuation_le_one _) zero_le
      _ = p.intValuation (u : R) := mul_one _
  simp [heightOneOrder, HeightOneSpectrum.valuation_of_algebraMap, hunit]

/-- Multiplying a rational Cartier local equation by a regular unit leaves its
actual principal Weil divisor unchanged. -/
theorem affinePrincipalDivisor_unit_transition {R : Type*} [CommRing R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (u : Rˣ) (a : Kˣ) :
    affinePrincipalDivisor (R := R) K (Units.map (algebraMap R K : R →* K) u * a) =
      affinePrincipalDivisor K a := by
  ext p
  change heightOneOrder K p _ = heightOneOrder K p a
  rw [heightOneOrder_mul, heightOneOrder_regular_unit, zero_add]

/-- Nonnegative local order is exactly the valuation's regularity condition. -/
theorem heightOneOrder_nonneg_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) (a : Kˣ) :
    0 ≤ heightOneOrder K p a ↔ p.valuation K (a : K) ≤ 1 := by
  have ha : p.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  rw [heightOneOrder, neg_nonneg, WithZero.log_le_iff_le_exp ha, WithZero.exp_zero]

/-- The actual principal divisor is effective precisely when its rational
function is regular in the affine coordinate ring. -/
theorem affinePrincipalDivisor_effective_iff {R : Type*} [CommRing R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) :
    (∀ p : HeightOneSpectrum R, 0 ≤ affinePrincipalDivisor K a p) ↔
      ∃ r : R, algebraMap R K r = (a : K) := by
  constructor
  · intro h
    exact HeightOneSpectrum.mem_integers_of_valuation_le_one K (a : K)
      (fun p => (heightOneOrder_nonneg_iff K p a).mp (h p))
  · rintro ⟨r, hr⟩ p
    apply (heightOneOrder_nonneg_iff K p a).mpr
    rw [← hr, HeightOneSpectrum.valuation_of_algebraMap]
    exact p.intValuation_le_one r

/-- Inverting the rational function negates the actual principal divisor. -/
theorem affinePrincipalDivisor_inv {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (a : Kˣ) :
    affinePrincipalDivisor (R := R) K a⁻¹ = -affinePrincipalDivisor K a := by
  ext p
  simp [affinePrincipalDivisor_apply, heightOneOrder, map_inv₀, WithZero.log_inv]

/-- A rational function has zero principal divisor exactly when it is a unit
of the actual affine coordinate ring. -/
theorem affinePrincipalDivisor_eq_zero_iff {R : Type*} [CommRing R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (a : Kˣ) :
    affinePrincipalDivisor (R := R) K a = 0 ↔
      ∃ u : Rˣ, Units.map (algebraMap R K : R →* K) u = a := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := (affinePrincipalDivisor_effective_iff (R := R) K a).mp
      (by intro p; simp [h])
    have hinv : affinePrincipalDivisor (R := R) K a⁻¹ = 0 := by
      rw [affinePrincipalDivisor_inv, h, neg_zero]
    obtain ⟨s, hs⟩ := (affinePrincipalDivisor_effective_iff (R := R) K a⁻¹).mp
      (by intro p; simp [hinv])
    have hrs : r * s = 1 := by
      apply IsFractionRing.injective R K
      simp [map_mul, hr, hs]
    refine ⟨⟨r, s, hrs, by simpa [mul_comm] using hrs⟩, ?_⟩
    exact Units.ext hr
  · rintro ⟨u, rfl⟩
    ext p
    exact heightOneOrder_regular_unit K p u

end Negativity
