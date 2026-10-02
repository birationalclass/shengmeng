module

public import Negativity.NormDivisor
public import Negativity.RationalProductFormula
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical

theorem polynomial_point_residueDegree (k : Type*) [Field k]
    (p : HeightOneSpectrum k[X]) (f : k[X]) (hf : p.asIdeal = Ideal.span {f}) :
    p.asIdeal.inertiaDeg k = f.natDegree := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (⊥ : Ideal k) p.asIdeal]
  have he : Module.finrank (k ⧸ (⊥ : Ideal k)) (k[X] ⧸ p.asIdeal) =
      Module.finrank k (k[X] ⧸ p.asIdeal) :=
    Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot k) (RingEquiv.refl _) (by
      ext x
      rfl)
  rw [he, hf, finrank_quotient_span_eq_natDegree]

noncomputable def polynomialPrimePoint {k : Type*} [Field k]
    (f : k[X]) (hf : Prime f) : HeightOneSpectrum k[X] :=
  ⟨Ideal.span {f}, Ideal.isPrime_of_prime (Ideal.prime_span_singleton_iff.mpr hf),
    by simpa using hf.ne_zero⟩

theorem polynomial_prime_principal_divisor (k K : Type*) [Field k]
    [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]
    (f : k[X]) (hf : Prime f) :
    affinePrincipalDivisor K (Units.mk0 (algebraMap k[X] K f)
      (by simpa using (IsFractionRing.injective k[X] K).ne hf.ne_zero)) =
      Finsupp.single (polynomialPrimePoint f hf) 1 := by
  rw [← idealFactorDivisor_principal k[X] K f hf.ne_zero]
  ext p
  rw [idealFactorDivisor_apply, multiplicity_eq_count_normalizedFactors p.irreducible
    (by simpa using hf.ne_zero)]
  have hs : Irreducible (Ideal.span {f} : Ideal k[X]) :=
    (Ideal.prime_span_singleton_iff.mpr hf).irreducible
  rw [normalize_eq, normalizedFactors_irreducible hs, normalize_eq,
    Multiset.count_singleton, Finsupp.single_apply]
  by_cases h : p = polynomialPrimePoint f hf
  · subst p; simp [polynomialPrimePoint]
  · have hi : p.asIdeal ≠ Ideal.span {f} := by
      intro he
      exact h (HeightOneSpectrum.ext he)
    simp [Ne.symm h, hi]

theorem polynomial_prime_principal_degree (k K : Type*) [Field k]
    [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]
    (f : k[X]) (hf : Prime f) :
    affineDivisorDegree k k[X] (affinePrincipalDivisor K
      (Units.mk0 (algebraMap k[X] K f)
        (by simpa using (IsFractionRing.injective k[X] K).ne hf.ne_zero))) =
      (f.natDegree : ℤ) := by
  rw [polynomial_prime_principal_divisor k K f hf, affineDivisorDegree_single,
    polynomial_point_residueDegree k _ f rfl, one_mul]

/-- The sum of actual local orders, weighted by actual residue degrees,
equals polynomial degree. This is independent of a chosen factorization. -/
theorem polynomial_principal_degree (k K : Type*) [Field k]
    [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]
    (f : k[X]) (hf : f ≠ 0) :
    affineDivisorDegree k k[X] (affinePrincipalDivisor K
      (Units.mk0 (algebraMap k[X] K f)
        (by simpa using (IsFractionRing.injective k[X] K).ne hf))) =
      (f.natDegree : ℤ) := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hf rfl).elim
  | h₂ f hu =>
    obtain ⟨u, rfl⟩ := hu
    have he : Units.mk0 (algebraMap k[X] K (u : k[X]))
        (by simp) =
        Units.map (algebraMap k[X] K : k[X] →* K) u := by
      apply Units.ext; rfl
    have hz : affinePrincipalDivisor (R := k[X]) K
        (Units.map (algebraMap k[X] K : k[X] →* K) u) = 0 := by
      ext p
      exact heightOneOrder_regular_unit K p u
    rw [he, hz, map_zero]
    simp
  | h₃ f p hf0 hp ih =>
    have he : Units.mk0 (algebraMap k[X] K (p * f))
        (by simpa using (IsFractionRing.injective k[X] K).ne hf) =
        Units.mk0 (algebraMap k[X] K p)
          (by simpa using (IsFractionRing.injective k[X] K).ne hp.ne_zero) *
        Units.mk0 (algebraMap k[X] K f)
          (by simpa using (IsFractionRing.injective k[X] K).ne hf0) := by
      apply Units.ext
      simp
    rw [he, affinePrincipalDivisor_mul, map_add,
      polynomial_prime_principal_degree k K p hp, ih hf0,
      Polynomial.natDegree_mul hp.ne_zero hf0, Nat.cast_add]

/-- The genuine affine principal divisor on A¹ has degree deg(num)-deg(denom). -/
theorem rational_affine_principal_degree (k : Type*) [Field k]
    (a : (RatFunc k)ˣ) :
    affineDivisorDegree k k[X] (affinePrincipalDivisor (RatFunc k) a) =
      (a : RatFunc k).intDegree := by
  have hn := RatFunc.num_ne_zero a.ne_zero
  have hd := RatFunc.denom_ne_zero (a : RatFunc k)
  let u := Units.mk0 (algebraMap k[X] (RatFunc k) (a : RatFunc k).num)
    (by simpa only [map_zero] using (IsFractionRing.injective k[X] (RatFunc k)).ne hn)
  let v := Units.mk0 (algebraMap k[X] (RatFunc k) (a : RatFunc k).denom)
    (by simpa only [map_zero] using (IsFractionRing.injective k[X] (RatFunc k)).ne hd)
  have he : a = u * v⁻¹ := by
    apply Units.ext
    simpa [u, v, div_eq_mul_inv] using (RatFunc.num_div_denom (a : RatFunc k)).symm
  conv_lhs => rw [he, affinePrincipalDivisor_mul, affinePrincipalDivisor_inv, map_add, map_neg]
  dsimp [u, v]
  rw [polynomial_principal_degree k (RatFunc k) _ hn,
    polynomial_principal_degree k (RatFunc k) _ hd]
  simp [RatFunc.intDegree, sub_eq_add_neg]

/-- Product formula on P¹ using actual closed-point divisor coefficients
and the actual normalized valuation at infinity. -/
theorem rational_actual_principal_degree_zero (k : Type*) [Field k]
    (a : (RatFunc k)ˣ) :
    affineDivisorDegree k k[X] (affinePrincipalDivisor (RatFunc k) a) +
      rationalInfinityOrder (a : RatFunc k) = 0 := by
  rw [rational_affine_principal_degree, rationalInfinityOrder_eq _ a.ne_zero]
  omega

end Negativity
