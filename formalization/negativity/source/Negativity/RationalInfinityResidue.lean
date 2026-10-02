module

public import Negativity.InfinityNorm
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Every rational function regular at infinity is congruent to a unique
constant modulo the actual infinity maximal ideal. Existence is proved
by cancelling the leading numerator and denominator coefficients. -/
theorem rational_infinity_approximate_constant (k : Type*) [Field k]
    (a : RatFunc k) (ha : RatFunc.inftyValuation k a ≤ 1) :
    ∃ c : k, RatFunc.inftyValuation k (a - RatFunc.C c) < 1 := by
  by_cases hlt : RatFunc.inftyValuation k a < 1
  · exact ⟨0, by simpa using hlt⟩
  have hv : RatFunc.inftyValuation k a = 1 := le_antisymm ha (le_of_not_gt hlt)
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at hv
  have hid : a.intDegree = 0 := by
    apply WithZero.exp_injective
    simpa only [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero k ha0,
      WithZero.exp_zero] using hv
  let p := a.num
  let q := a.denom
  have hp : p ≠ 0 := RatFunc.num_ne_zero ha0
  have hq : q ≠ 0 := RatFunc.denom_ne_zero a
  have hnd : p.natDegree = q.natDegree := by
    dsimp [RatFunc.intDegree] at hid
    dsimp [p, q]
    omega
  have hd : p.degree = q.degree := by
    rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, hnd]
  let c := p.leadingCoeff / q.leadingCoeff
  have hc : c ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp)
    (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hdC : (Polynomial.C c * q).degree = q.degree :=
    Polynomial.degree_C_mul_of_isUnit (IsUnit.mk0 c hc) q
  have hlc : p.leadingCoeff = (Polynomial.C c * q).leadingCoeff := by
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit (IsUnit.mk0 c hc)]
    dsimp [c]
    rw [div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hq)]
  let g := p - Polynomial.C c * q
  have hgdeg : g.degree < q.degree := by
    exact (Polynomial.degree_sub_lt_left (hd.trans hdC.symm) hp hlc).trans_eq hd
  have hqmap : algebraMap k[X] (RatFunc k) q ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective k[X] (RatFunc k)).ne hq
  have hre : a - RatFunc.C c =
      algebraMap k[X] (RatFunc k) g / algebraMap k[X] (RatFunc k) q := by
    have hrepr : a = algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q :=
      (RatFunc.num_div_denom a).symm
    rw [hrepr]
    dsimp [g]
    simp only [map_sub, map_mul, RatFunc.algebraMap_C]
    field_simp
  refine ⟨c, ?_⟩
  by_cases hg : g = 0
  · rw [hre, hg]
    simp
  have hgmap : algebraMap k[X] (RatFunc k) g ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective k[X] (RatFunc k)).ne hg
  have hgn : g.natDegree < q.natDegree := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hg]
    simpa only [Polynomial.degree_eq_natDegree hq] using hgdeg
  rw [hre, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero k (div_ne_zero hgmap hqmap),
    RatFunc.intDegree_div hgmap hqmap, RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, ← WithZero.exp_zero]
  apply WithZero.exp_lt_exp.mpr
  exact sub_neg.mpr (by exact_mod_cast hgn)

noncomputable def rationalInfinityConstantHom (k : Type*) [Field k] :
    k →+* RationalInfinityRing k :=
  (algebraMap k (RatFunc k)).codRestrict (RatFunc.inftyValuation k).valuationSubring.toSubring
    (fun c => by
      change RatFunc.inftyValuation k (algebraMap k (RatFunc k) c) ≤ 1
      exact Valuation.IsTrivialOn.valuation_algebraMap_le_one _ c)

noncomputable instance rationalInfinityConstantAlgebra (k : Type*) [Field k] :
    Algebra k (RationalInfinityRing k) := (rationalInfinityConstantHom k).toAlgebra

/-- The actual infinity residue field is k, via the actual constant map. -/
theorem rational_infinity_residue_constants_bijective (k : Type*) [Field k] :
    Function.Bijective ((IsLocalRing.residue (RationalInfinityRing k)).comp
      (rationalInfinityConstantHom k)) := by
  refine ⟨RingHom.injective _, ?_⟩
  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨c, hc⟩ := rational_infinity_approximate_constant k (a : RatFunc k) a.2
  refine ⟨c, ?_⟩
  change IsLocalRing.residue (RationalInfinityRing k) (rationalInfinityConstantHom k c) =
    IsLocalRing.residue (RationalInfinityRing k) a
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff,
    (RatFunc.inftyValuation k).mem_maximalIdeal_iff]
  change RatFunc.inftyValuation k (RatFunc.C c - (a : RatFunc k)) < 1
  rw [← neg_sub, Valuation.map_neg]
  exact hc

theorem rational_infinity_residue_degree_one (k : Type*) [Field k] :
    Module.finrank k (IsLocalRing.ResidueField (RationalInfinityRing k)) = 1 := by
  let e : k ≃ₐ[k] IsLocalRing.ResidueField (RationalInfinityRing k) :=
    AlgEquiv.ofBijective (Algebra.ofId k _)
      (rational_infinity_residue_constants_bijective k)
  rw [← e.toLinearEquiv.finrank_eq]
  exact Module.finrank_self k

theorem rational_infinity_inertia_degree_one (k : Type*) [Field k] :
    (IsLocalRing.maximalIdeal (RationalInfinityRing k)).inertiaDeg k = 1 := by
  have : (IsLocalRing.maximalIdeal (RationalInfinityRing k)).LiesOver (⊥ : Ideal k) := inferInstance
  rw [Ideal.inertiaDeg_eq_of_isMaximal (⊥ : Ideal k)
    (IsLocalRing.maximalIdeal (RationalInfinityRing k))]
  have he : Module.finrank (k ⧸ (⊥ : Ideal k))
      ((RationalInfinityRing k) ⧸ IsLocalRing.maximalIdeal (RationalInfinityRing k)) =
      Module.finrank k ((RationalInfinityRing k) ⧸ IsLocalRing.maximalIdeal (RationalInfinityRing k)) :=
    Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot k) (RingEquiv.refl _) (by
      ext x
      rfl)
  rw [he]
  exact rational_infinity_residue_degree_one k

/-- The infinity norm coefficient is exactly the actual k-residue-weighted
sum upstairs. No separate equality of residue weights is assumed. -/
theorem infinity_pushforward_degree (k B : Type*) [Field k]
    [CommRing B] [IsDedekindDomain B] [Algebra (RationalInfinityRing k) B]
    [Module.Finite (RationalInfinityRing k) B] [Algebra k B]
    [IsScalarTower k (RationalInfinityRing k) B]
    (D : IsDedekindDomain.HeightOneSpectrum B →₀ ℤ) :
    affineDivisorDegree k B D =
      (affineDivisorPushforward (RationalInfinityRing k) B D)
        (IsDiscreteValuationRing.maximalIdeal (RationalInfinityRing k)) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, Finsupp.coe_add, Pi.add_apply, hD, hE]
  | single q n =>
    have hq : (q.under (RationalInfinityRing k)).asIdeal =
        IsLocalRing.maximalIdeal (RationalInfinityRing k) :=
      IsLocalRing.eq_maximalIdeal (q.under (RationalInfinityRing k)).isMaximal
    have hqp : q.under (RationalInfinityRing k) =
        IsDiscreteValuationRing.maximalIdeal (RationalInfinityRing k) := by
      exact IsDedekindDomain.HeightOneSpectrum.ext hq
    have : q.asIdeal.LiesOver (q.under (RationalInfinityRing k)).asIdeal := ⟨rfl⟩
    have ht := Ideal.inertiaDeg_tower (R := k)
      (q.under (RationalInfinityRing k)).asIdeal q.asIdeal
    rw [hq, rational_infinity_inertia_degree_one, one_mul] at ht
    rw [affineDivisorDegree_single, affineDivisorPushforward_single, hqp,
      Finsupp.single_eq_same, ht]

/-- Product formula with actual residue degrees over k at every place,
including all places over infinity. The curve/Scheme identification is
separate; the previous infinity-residue weight bridge is now eliminated. -/
theorem twoChart_baseField_principal_degree_zero (k S B L : Type*) [Field k]
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
    [Algebra k B] [IsScalarTower k (RationalInfinityRing k) B]
    [Algebra.IsSeparable (RatFunc k) L] (a : Lˣ) :
    affineDivisorDegree k S (affinePrincipalDivisor L a) +
      affineDivisorDegree k B (affinePrincipalDivisor L a) = 0 := by
  rw [infinity_pushforward_degree k B (affinePrincipalDivisor L a)]
  exact twoChart_principal_degree_zero k S B L a

/-- Actual points over infinity have residue degree one over an
algebraically closed base. Finiteness is derived from the finite extension
of the infinity DVR, without assuming its integral closure finite-type over k. -/
theorem algebraicallyClosed_infinity_point_degree_one (k B : Type*)
    [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
    [Algebra (RationalInfinityRing k) B] [Module.Finite (RationalInfinityRing k) B]
    [Algebra k B] [IsScalarTower k (RationalInfinityRing k) B]
    (q : IsDedekindDomain.HeightOneSpectrum B) : q.asIdeal.inertiaDeg k = 1 := by
  have hq : (q.under (RationalInfinityRing k)).asIdeal =
      IsLocalRing.maximalIdeal (RationalInfinityRing k) :=
    IsLocalRing.eq_maximalIdeal (q.under (RationalInfinityRing k)).isMaximal
  have : q.asIdeal.LiesOver (q.under (RationalInfinityRing k)).asIdeal := ⟨rfl⟩
  have ht := Ideal.inertiaDeg_tower (R := k)
    (q.under (RationalInfinityRing k)).asIdeal q.asIdeal
  rw [hq, rational_infinity_inertia_degree_one, one_mul] at ht
  have hp : 0 < q.asIdeal.inertiaDeg k := by
    rw [ht]
    exact Ideal.inertiaDeg_pos q.asIdeal (RationalInfinityRing k)
  let : Field (B ⧸ q.asIdeal) := Ideal.Quotient.field q.asIdeal
  have he : Module.finrank (k ⧸ (⊥ : Ideal k)) (B ⧸ q.asIdeal) =
      Module.finrank k (B ⧸ q.asIdeal) :=
    Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot k) (RingEquiv.refl _) (by
      ext x
      rfl)
  rw [Ideal.inertiaDeg_eq_of_isMaximal (⊥ : Ideal k) q.asIdeal, he] at hp ⊢
  let : Module.Finite k (B ⧸ q.asIdeal) := Module.finite_of_finrank_pos hp
  let e : k ≃ₐ[k] (B ⧸ q.asIdeal) :=
    AlgEquiv.ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  simpa using e.toLinearEquiv.finrank_eq.symm

theorem affineDivisorDegree_eq_order_sum (k R : Type*) [Field k] [CommRing R]
    [IsDedekindDomain R] [Algebra k R]
    (h : ∀ p : IsDedekindDomain.HeightOneSpectrum R, p.asIdeal.inertiaDeg k = 1)
    (D : IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :
    affineDivisorDegree k R D = D.degree := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, hD, hE]
  | single p n => simp [affineDivisorDegree_single, h, Finsupp.degree_single]

end Negativity
