module

public import Negativity.RationalDivisor
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain UniqueFactorizationMonoid Polynomial
open scoped Classical WithZero

/-- The actual local ring of the infinity place of k(t). -/
noncomputable abbrev RationalInfinityRing (k : Type*) [Field k] :=
  (RatFunc.inftyValuation k).valuationSubring

/-- A rank-one valuation whose uniformizer has value exp(-1) agrees
exactly with the normalized adic valuation of its actual valuation ring. -/
theorem normalized_discrete_valuation_eq (K : Type*) [Field K]
    (v : Valuation K ℤᵐ⁰) [v.IsNontrivial] (π : K)
    (hπ : v π = WithZero.exp (-1 : ℤ)) :
    (IsDiscreteValuationRing.maximalIdeal v.valuationSubring).valuation K = v := by
  let A := v.valuationSubring
  let : IsDiscreteValuationRing A := inferInstance
  let p := IsDiscreteValuationRing.maximalIdeal A
  have hmem : π ∈ v.valuationSubring := by
    change v π ≤ 1
    rw [hπ]
    decide
  let πA : A := ⟨π, hmem⟩
  have hu : v.IsUniformizer π := by
    rw [Valuation.IsUniformizer.iff,
      Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
        (v := v) ⟨π, hπ⟩]
    exact hπ
  have hgen : p.asIdeal = Ideal.span {πA} := by
    exact Valuation.IsUniformizer.is_generator (v := v) (π := πA) hu
  have hpv : p.valuation K π = WithZero.exp (-1 : ℤ) := by
    change p.valuation K (algebraMap A K πA) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have hn : πA ≠ 0 := by
      intro hz
      have hz' : π = 0 := congrArg (fun x : A => (x : K)) hz
      rw [hz', map_zero] at hπ
      exact (WithZero.exp_ne_zero (a := (-1 : ℤ))) hπ.symm
    rw [p.intValuation_eq_exp_neg_multiplicity hn, ← hgen,
      multiplicity_eq_count_normalizedFactors p.irreducible p.ne_bot,
      normalize_eq, normalizedFactors_irreducible p.irreducible, normalize_eq]
    simp
  have he : (p.valuation K).IsEquiv v := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
      rw [← ha]
      exact a.2
    · intro hx
      let a : A := ⟨x, hx⟩
      exact p.valuation_le_one a
  ext x
  by_cases hx : x = 0
  · simp [hx]
  have hvx : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  let n : ℤ := WithZero.log (v x)
  have hpow : v (π ^ (-n)) = v x := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id, neg_mul_neg, mul_one]
    exact WithZero.exp_log hvx
  have hadic : p.valuation K (π ^ (-n)) = v x := by
    rw [map_zpow₀, hpv, ← WithZero.exp_zsmul]
    simp only [zsmul_eq_mul, Int.cast_id, neg_mul_neg, mul_one]
    exact WithZero.exp_log hvx
  exact ((he.eq_iff).mpr hpow).symm.trans hadic

theorem rational_infinity_normalized_valuation (k : Type*) [Field k] :
    (IsDiscreteValuationRing.maximalIdeal (RationalInfinityRing k)).valuation (RatFunc k) =
      RatFunc.inftyValuation k := by
  exact normalized_discrete_valuation_eq (RatFunc k) (RatFunc.inftyValuation k)
    (1 / RatFunc.X) (RatFunc.inftyValuation.X_inv k)

/-- The actual order at infinity, expressed in the local-ring language
used by the ideal norm and principal divisor constructions. -/
theorem rational_infinity_heightOneOrder (k : Type*) [Field k]
    (a : (RatFunc k)ˣ) :
    heightOneOrder (RatFunc k)
      (IsDiscreteValuationRing.maximalIdeal (RationalInfinityRing k)) a =
      rationalInfinityOrder (a : RatFunc k) := by
  unfold heightOneOrder rationalInfinityOrder
  rw [rational_infinity_normalized_valuation]

/-- Infinity order of the function norm equals the actual weighted
pushforward coefficient of the local principal divisor upstairs. -/
theorem separable_infinity_principal_norm (k B L : Type*) [Field k]
    [CommRing B] [IsDedekindDomain B] [Field L]
    [Algebra (RationalInfinityRing k) B] [Module.Finite (RationalInfinityRing k) B]
    [Module.IsTorsionFree (RationalInfinityRing k) B]
    [Algebra B L] [IsFractionRing B L] [Algebra (RatFunc k) L]
    [Algebra (RationalInfinityRing k) L]
    [IsScalarTower (RationalInfinityRing k) (RatFunc k) L]
    [IsScalarTower (RationalInfinityRing k) B L]
    [Algebra.IsSeparable (RatFunc k) L] (a : Lˣ) :
    (affineDivisorPushforward (RationalInfinityRing k) B (affinePrincipalDivisor L a))
        (IsDiscreteValuationRing.maximalIdeal (RationalInfinityRing k)) =
      rationalInfinityOrder (functionFieldNormUnits (RatFunc k) L a : RatFunc k) := by
  rw [← separable_functionField_principal_norm (RationalInfinityRing k) B (RatFunc k) L,
    affinePrincipalDivisor_apply, rational_infinity_heightOneOrder]

/-- Product formula for an actual affine normal chart and actual normal
local chart above infinity, in one finite separable function field. All
orders, norms and residue weights are computed, not assumed identities.
This still requires geometric identification of these charts with a given
complete Scheme curve before it can define degree of its line bundles. -/
theorem twoChart_principal_degree_zero (k S B L : Type*) [Field k]
    [CommRing S] [IsDedekindDomain S] [CommRing B] [IsDedekindDomain B] [Field L]
    [Algebra k S] [Algebra.FiniteType k S]
    [Algebra k[X] S] [IsScalarTower k k[X] S]
    [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S]
    [Algebra S L] [IsFractionRing S L] [Algebra (RatFunc k) L]
    [Algebra k[X] L] [IsScalarTower k[X] (RatFunc k) L] [IsScalarTower k[X] S L]
    [Algebra (RationalInfinityRing k) B] [Module.Finite (RationalInfinityRing k) B]
    [Module.IsTorsionFree (RationalInfinityRing k) B]
    [Algebra B L] [IsFractionRing B L] [Algebra (RationalInfinityRing k) L]
    [IsScalarTower (RationalInfinityRing k) (RatFunc k) L]
    [IsScalarTower (RationalInfinityRing k) B L]
    [Algebra.IsSeparable (RatFunc k) L] (a : Lˣ) :
    affineDivisorDegree k S (affinePrincipalDivisor L a) +
      (affineDivisorPushforward (RationalInfinityRing k) B (affinePrincipalDivisor L a))
        (IsDiscreteValuationRing.maximalIdeal (RationalInfinityRing k)) = 0 := by
  rw [separable_infinity_principal_norm k B L a,
    ← separable_functionField_principal_norm_degree k k[X] S (RatFunc k) L a]
  exact rational_actual_principal_degree_zero k (functionFieldNormUnits (RatFunc k) L a)

end Negativity
