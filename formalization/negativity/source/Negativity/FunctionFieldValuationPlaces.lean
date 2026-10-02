module

public import Negativity.ValuationChartCover
public import Negativity.DedekindValuationPlaces
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain Polynomial
set_option backward.isDefEq.respectTransparency false
noncomputable section

local instance (priority := low) (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] : Algebra k[X] L :=
  ((algebraMap (RatFunc k) L).comp (algebraMap k[X] (RatFunc k))).toAlgebra
local instance (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L] :
    IsScalarTower k[X] (RatFunc k) L := IsScalarTower.of_algebraMap_eq' rfl
local instance (priority := low) (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] : Algebra (RationalInfinityRing k) L :=
  ((algebraMap (RatFunc k) L).comp
    (algebraMap (RationalInfinityRing k) (RatFunc k))).toAlgebra
local instance (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L] :
    IsScalarTower (RationalInfinityRing k) (RatFunc k) L :=
  IsScalarTower.of_algebraMap_eq' rfl

namespace FunctionFieldPlaces
variable (k L : Type*) [Field k] [Field L] [Algebra (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] [Algebra.IsSeparable (RatFunc k) L]

/-- Actual normalization primes on the finite chart and the infinity chart. -/
abbrev TwoChartPlace := HeightOneSpectrum (FiniteRing k L) ⊕
  HeightOneSpectrum (InfinityRing k L)

/-- Both chart primes define valuation subrings of the same actual function field. -/
def twoChartValuation : TwoChartPlace k L → ValuationSubring L
  | .inl p => (p.valuation L).valuationSubring
  | .inr q => (q.valuation L).valuationSubring

end FunctionFieldPlaces

theorem finite_place_parameter_regular (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L]
    (p : HeightOneSpectrum (FunctionFieldPlaces.FiniteRing k L)) :
    algebraMap (RatFunc k) L RatFunc.X ∈ (p.valuation L).valuationSubring := by
  have h := p.valuation_le_one (K := L)
    (algebraMap k[X] (FunctionFieldPlaces.FiniteRing k L) Polynomial.X)
  change p.valuation L (algebraMap (FunctionFieldPlaces.FiniteRing k L) L
    (algebraMap k[X] (FunctionFieldPlaces.FiniteRing k L) Polynomial.X)) ≤ 1 at h
  rw [← IsScalarTower.algebraMap_apply] at h
  exact h

/-- Every actual infinity prime has a pole of the parameter. Its contraction
is the infinity maximal ideal; the inverse parameter is in that ideal. -/
theorem infinity_place_parameter_pole (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L]
    (q : HeightOneSpectrum (FunctionFieldPlaces.InfinityRing k L)) :
    algebraMap (RatFunc k) L RatFunc.X ∉ (q.valuation L).valuationSubring := by
  classical
  let A := RationalInfinityRing k
  let B := FunctionFieldPlaces.InfinityRing k L
  let s : A := ⟨1 / RatFunc.X, by
    change RatFunc.inftyValuation k (1 / RatFunc.X) ≤ 1
    rw [RatFunc.inftyValuation.X_inv k]
    decide⟩
  have hs : s ∈ IsLocalRing.maximalIdeal A := by
    rw [(RatFunc.inftyValuation k).mem_maximalIdeal_iff]
    change RatFunc.inftyValuation k (1 / RatFunc.X) < 1
    rw [RatFunc.inftyValuation.X_inv k]
    decide
  have hq : (q.under A).asIdeal = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (q.under A).isMaximal
  have hsq : algebraMap A B s ∈ q.asIdeal := by
    exact (show s ∈ (q.under A).asIdeal from hq ▸ hs)
  have hv := (q.valuation_lt_one_iff_mem (K := L) (algebraMap A B s)).mpr hsq
  change q.valuation L (algebraMap B L (algebraMap A B s)) < 1 at hv
  have hsmap : algebraMap B L (algebraMap A B s) =
      (algebraMap (RatFunc k) L RatFunc.X)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A (RatFunc k) L]
    simp [s]
  rw [hsmap, map_inv₀] at hv
  have hx : q.valuation L (algebraMap (RatFunc k) L RatFunc.X) ≠ 0 := by
    apply (Valuation.ne_zero_iff _).mpr
    exact (map_ne_zero_iff _ (algebraMap (RatFunc k) L).injective).mpr RatFunc.X_ne_zero
  change ¬ q.valuation L (algebraMap (RatFunc k) L RatFunc.X) ≤ 1
  exact not_le_of_gt ((inv_lt_one₀ (pos_iff_ne_zero.mpr hx)).mp hv)

theorem twoChartValuation_injective (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] :
    Function.Injective (FunctionFieldPlaces.twoChartValuation k L) := by
  rintro (p | q) (p' | q') he
  · exact congrArg Sum.inl (HeightOneSpectrum.valuationSubring_valuation_injective L he)
  · change (p.valuation L).valuationSubring = (q'.valuation L).valuationSubring at he
    exact False.elim (infinity_place_parameter_pole k L q'
      (he ▸ finite_place_parameter_regular k L p))
  · change (q.valuation L).valuationSubring = (p'.valuation L).valuationSubring at he
    exact False.elim (infinity_place_parameter_pole k L q
      (he.symm ▸ finite_place_parameter_regular k L p'))
  · exact congrArg Sum.inr (HeightOneSpectrum.valuationSubring_valuation_injective L he)

theorem twoChartValuation_ne_top (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [FiniteDimensional (RatFunc k) L]
    [Algebra.IsSeparable (RatFunc k) L] (p : FunctionFieldPlaces.TwoChartPlace k L) :
    FunctionFieldPlaces.twoChartValuation k L p ≠ ⊤ := by
  cases p with
  | inl p =>
    intro he
    exact (Valuation.valuationSubring_eq_top_iff _).mp he inferInstance
  | inr q =>
    intro he
    exact (Valuation.valuationSubring_eq_top_iff _).mp he inferInstance

theorem twoChartValuation_contains_constants (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [Algebra k L] [IsScalarTower k (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] [Algebra.IsSeparable (RatFunc k) L]
    (p : FunctionFieldPlaces.TwoChartPlace k L) (c : k) :
    algebraMap k L c ∈ FunctionFieldPlaces.twoChartValuation k L p := by
  cases p with
  | inl p =>
    have h := p.valuation_le_one (K := L)
      (algebraMap k (FunctionFieldPlaces.FiniteRing k L) c)
    change p.valuation L ((algebraMap (RatFunc k) L) (algebraMap k (RatFunc k) c)) ≤ 1 at h
    rw [← IsScalarTower.algebraMap_apply] at h
    exact h
  | inr q =>
    have h := q.valuation_le_one (K := L)
      (algebraMap k (FunctionFieldPlaces.InfinityRing k L) c)
    change q.valuation L ((algebraMap (RatFunc k) L) (algebraMap k (RatFunc k) c)) ≤ 1 at h
    rw [← IsScalarTower.algebraMap_apply] at h
    exact h

/-- Final theorem: all nontrivial ground-field valuation rings of a finite
separable extension of k(t) arise from exactly one prime of exactly one of
the two actual integral-closure charts. No coverage or disjointness premise
is assumed. This classifies all places, not just some constructed places. -/
theorem functionField_valuation_unique_twoChart_place (k L : Type*) [Field k] [Field L]
    [Algebra (RatFunc k) L] [Algebra k L] [IsScalarTower k (RatFunc k) L]
    [FiniteDimensional (RatFunc k) L] [Algebra.IsSeparable (RatFunc k) L]
    (A : ValuationSubring L) (hA : A ≠ ⊤)
    (hk : ∀ c : k, algebraMap k L c ∈ A) :
    ∃! p : FunctionFieldPlaces.TwoChartPlace k L,
      FunctionFieldPlaces.twoChartValuation k L p = A := by
  have hex : ∃ p : FunctionFieldPlaces.TwoChartPlace k L,
      FunctionFieldPlaces.twoChartValuation k L p = A := by
    rcases functionField_valuation_integralClosure_chart_cover k L A hk with hfin | hinf
    · obtain ⟨p, hp, _⟩ := dedekind_chart_valuation_unique_prime
        (FunctionFieldPlaces.FiniteRing k L) L A hA hfin
      exact ⟨.inl p, hp⟩
    · obtain ⟨q, hq, _⟩ := dedekind_chart_valuation_unique_prime
        (FunctionFieldPlaces.InfinityRing k L) L A hA hinf
      exact ⟨.inr q, hq⟩
  obtain ⟨p, hp⟩ := hex
  exact ⟨p, hp, fun q hq ↦ twoChartValuation_injective k L (hq.trans hp.symm)⟩

end
end Negativity
