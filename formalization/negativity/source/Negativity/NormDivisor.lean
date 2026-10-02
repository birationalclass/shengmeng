module

public import Negativity.SeparableNorm
public import Negativity.DivisorPullback
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical
open scoped nonZeroDivisors
attribute [local instance] FractionRing.liftAlgebra

set_option backward.isDefEq.respectTransparency false

/-- Factorization of an actual ideal norm into the underlying prime ideals
with their inertia degrees. Separability of the extension suffices; no
perfectness of the base fraction field or characteristic-zero hypothesis. -/
theorem separable_relNorm_factorization (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (I : Ideal S) (hI : I ≠ ⊥) :
    Ideal.relNorm R I =
      ((normalizedFactors I).map (fun Q => (Q.under R) ^ Q.inertiaDeg R)).prod := by
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  rw [map_multiset_prod]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro Q hQ
  have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors hQ
  have : Q.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hQ).1
  have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 inferInstance
  have hp0 : Q.under R ≠ ⊥ := Ideal.IsIntegral.under_ne_bot R hQ0
  have : (Q.under R).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp0 inferInstance
  exact separable_prime_ideal_norm R S Q (Q.under R)

/-- The order of a prime power, with both primes actual Dedekind points. -/
theorem ideal_primePower_multiplicity (R : Type*) [CommRing R] [IsDedekindDomain R]
    (p q : HeightOneSpectrum R) (n : ℕ) :
    multiplicity p.asIdeal (q.asIdeal ^ n) = if p = q then n else 0 := by
  rw [multiplicity_eq_count_normalizedFactors p.irreducible (pow_ne_zero n q.ne_bot),
    normalizedFactors_pow, normalizedFactors_irreducible q.irreducible]
  by_cases h : p = q
  · subst q
    simp
  · have hpq : p.asIdeal ≠ q.asIdeal := fun he => h (HeightOneSpectrum.ext he)
    simp [h, hpq]

/-- Order of a product of prime powers: every contribution is counted with
its multiplicity. This will be used on the actual ideal norm factorization. -/
theorem ideal_primePower_product_multiplicity (R : Type*)
    [CommRing R] [IsDedekindDomain R] (p : HeightOneSpectrum R)
    {α : Type*} (M : Multiset α) (point : α → HeightOneSpectrum R) (n : α → ℕ) :
    multiplicity p.asIdeal ((M.map fun q => (point q).asIdeal ^ n q).prod) =
      (M.map fun q => if p = point q then n q else 0).sum := by
  have hne (M : Multiset α) :
      (M.map fun q => (point q).asIdeal ^ n q).prod ≠ (0 : Ideal R) := by
    induction M using Multiset.induction_on with
    | empty => simp
    | cons q M ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact mul_ne_zero (pow_ne_zero _ (point q).ne_bot) ih
  induction M using Multiset.induction_on with
  | empty => simp
  | cons q M ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [multiplicity_mul p.prime (FiniteMultiplicity.of_prime_left p.prime
      (mul_ne_zero (pow_ne_zero _ (point q).ne_bot) (hne M))),
      ideal_primePower_multiplicity, ih]

/-- The actual prime factors of a nonzero ideal, retaining repeated factors. -/
noncomputable def normalizedIdealPoints (R : Type*) [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) : Multiset (HeightOneSpectrum R) :=
  (normalizedFactors I).attach.map fun Q =>
    ⟨Q.1, ((Ideal.mem_normalizedFactors_iff hI).mp Q.2).1,
      ne_zero_of_mem_normalizedFactors Q.2⟩

theorem normalizedIdealPoints_asIdeal (R : Type*) [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) :
    (normalizedIdealPoints R I hI).map HeightOneSpectrum.asIdeal = normalizedFactors I := by
  simp [normalizedIdealPoints, Multiset.map_map]

/-- The norm's order at each actual target point, computed from source
prime factors with inertia degrees. The norm compatibility is proved. -/
theorem separable_ideal_norm_order (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (I : Ideal S) (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    multiplicity p.asIdeal (Ideal.relNorm R I) =
      ((normalizedIdealPoints S I hI).map fun q =>
        if p = q.under R then q.asIdeal.inertiaDeg R else 0).sum := by
  have hn : Ideal.relNorm R I =
      ((normalizedIdealPoints S I hI).map fun q =>
        (q.under R).asIdeal ^ q.asIdeal.inertiaDeg R).prod := by
    rw [separable_relNorm_factorization R S I hI]
    have hmap := normalizedIdealPoints_asIdeal S I hI
    rw [← hmap, Multiset.map_map]
    rfl
  rw [hn, ideal_primePower_product_multiplicity]

/-- Integral local equations have orders given by the actual prime ideal
multiplicity of their principal ideals. -/
theorem heightOneOrder_regular_eq_multiplicity (R K : Type*)
    [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) (a : R) (ha : a ≠ 0) :
    heightOneOrder K p
      (Units.mk0 (algebraMap R K a) (by simpa using (IsFractionRing.injective R K).ne ha)) =
      (multiplicity p.asIdeal (Ideal.span {a}) : ℤ) := by
  simp [heightOneOrder, HeightOneSpectrum.valuation_of_algebraMap,
    p.intValuation_eq_exp_neg_multiplicity ha]

/-- Order of the norm of a nonzero integral rational equation. This is the
local function-norm computation needed to transport the product formula. -/
theorem separable_integral_norm_order (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (a : S) (ha : a ≠ 0) (p : HeightOneSpectrum R) :
    heightOneOrder (FractionRing R) p
      (Units.mk0 (algebraMap R (FractionRing R) (Algebra.intNorm R S a))
        (by simpa using (IsFractionRing.injective R (FractionRing R)).ne (Algebra.intNorm_ne_zero.mpr ha))) =
      (((normalizedIdealPoints S (Ideal.span {a}) (by simpa using ha)).map fun q =>
        if p = q.under R then q.asIdeal.inertiaDeg R else 0).sum : ℤ) := by
  rw [heightOneOrder_regular_eq_multiplicity R (FractionRing R) p _
    (Algebra.intNorm_ne_zero.mpr ha)]
  have h := separable_ideal_norm_order R S (Ideal.span {a}) (by simpa using ha) p
  rw [Ideal.relNorm_singleton] at h
  have hc := congrArg (fun n : ℕ => (n : ℤ)) h
  simpa only [Nat.cast_multiset_sum, Multiset.map_map, Function.comp_def,
    apply_ite, Nat.cast_zero] using hc

theorem ideal_order_eq_point_count (R : Type*) [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    multiplicity p.asIdeal I = (normalizedIdealPoints R I hI).count p := by
  rw [multiplicity_eq_count_normalizedFactors p.irreducible hI, normalize_eq,
    ← normalizedIdealPoints_asIdeal R I hI,
    Multiset.count_map_eq_count' _ _ HeightOneSpectrum.asIdeal_injective]

/-- The actual integral Weil divisor associated with a nonzero ideal. -/
noncomputable def idealFactorDivisor (R : Type*) [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) : HeightOneSpectrum R →₀ ℤ :=
  ((normalizedIdealPoints R I hI).map fun p => Finsupp.single p (1 : ℤ)).sum

theorem idealFactorDivisor_apply (R : Type*) [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) (p : HeightOneSpectrum R) :
    idealFactorDivisor R I hI p = (multiplicity p.asIdeal I : ℤ) := by
  rw [ideal_order_eq_point_count R I hI p]
  unfold idealFactorDivisor
  generalize normalizedIdealPoints R I hI = M
  induction M using Multiset.induction_on with
  | empty => simp
  | cons q M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih, Multiset.count_cons]
    by_cases h : q = p
    · subst q
      simp [add_comm]
    · simp [Ne.symm h]

theorem idealFactorDivisor_principal (R K : Type*)
    [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (a : R) (ha : a ≠ 0) :
    idealFactorDivisor R (Ideal.span {a}) (by simpa using ha) =
      affinePrincipalDivisor K (Units.mk0 (algebraMap R K a)
        (by simpa using (IsFractionRing.injective R K).ne ha)) := by
  ext p
  rw [idealFactorDivisor_apply, affinePrincipalDivisor_apply,
    heightOneOrder_regular_eq_multiplicity R K p a ha]

/-- Actual finite affine-curve cycle pushforward: points map to their
contracted prime and carry the residue-field degree. -/
noncomputable def affineDivisorPushforward (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] :
    (HeightOneSpectrum S →₀ ℤ) →+ (HeightOneSpectrum R →₀ ℤ) :=
  Finsupp.liftAddHom fun q => zmultiplesHom _
    (Finsupp.single (q.under R) (q.asIdeal.inertiaDeg R : ℤ))

theorem affineDivisorPushforward_single (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] (q : HeightOneSpectrum S) (n : ℤ) :
    affineDivisorPushforward R S (Finsupp.single q n) =
      Finsupp.single (q.under R) (n * (q.asIdeal.inertiaDeg R : ℤ)) := by
  simp [affineDivisorPushforward]

theorem separable_ideal_norm_divisor (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (I : Ideal S) (hI : I ≠ ⊥) :
    idealFactorDivisor R (Ideal.relNorm R I) (Ideal.relNorm_eq_bot_iff.not.mpr hI) =
      affineDivisorPushforward R S (idealFactorDivisor S I hI) := by
  ext p
  rw [idealFactorDivisor_apply, separable_ideal_norm_order R S I hI p]
  change _ = (Finsupp.applyAddHom p) (affineDivisorPushforward R S _)
  simp only [idealFactorDivisor, map_multiset_sum, Multiset.map_map,
    Function.comp_def, affineDivisorPushforward_single, one_mul,
    Finsupp.applyAddHom_apply, Finsupp.single_apply]
  push_cast
  simp [eq_comm]

noncomputable def fractionFieldNormUnits (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S] :
    (FractionRing S)ˣ →* (FractionRing R)ˣ :=
  Units.map (Algebra.norm (FractionRing R) : FractionRing S →* FractionRing R)

theorem fractionFieldNormUnits_integral (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (a : S) (ha : a ≠ 0) :
    fractionFieldNormUnits R S (Units.mk0 (algebraMap S (FractionRing S) a)
      (by simpa using (IsFractionRing.injective S (FractionRing S)).ne ha)) =
      Units.mk0 (algebraMap R (FractionRing R) (Algebra.intNorm R S a))
        (by simpa using (IsFractionRing.injective R (FractionRing R)).ne (Algebra.intNorm_ne_zero.mpr ha)) := by
  apply Units.ext
  exact (Algebra.algebraMap_intNorm_fractionRing a).symm

theorem separable_integral_principal_norm (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (a : S) (ha : a ≠ 0) :
    affinePrincipalDivisor (FractionRing R)
      (fractionFieldNormUnits R S (Units.mk0 (algebraMap S (FractionRing S) a)
        (by simpa using (IsFractionRing.injective S (FractionRing S)).ne ha))) =
      affineDivisorPushforward R S
        (affinePrincipalDivisor (FractionRing S) (Units.mk0 (algebraMap S (FractionRing S) a)
          (by simpa using (IsFractionRing.injective S (FractionRing S)).ne ha))) := by
  rw [fractionFieldNormUnits_integral R S a ha]
  have h := separable_ideal_norm_divisor R S (Ideal.span {a}) (by simpa using ha)
  simpa only [Ideal.relNorm_singleton,
    idealFactorDivisor_principal R (FractionRing R) _ (Algebra.intNorm_ne_zero.mpr ha),
    idealFactorDivisor_principal S (FractionRing S) a ha] using h

/-- The affine norm/divisor formula for EVERY nonzero rational function,
not only regular equations. The maps, orders and residue degrees are actual. -/
theorem separable_affine_principal_norm (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (a : (FractionRing S)ˣ) :
    affinePrincipalDivisor (FractionRing R) (fractionFieldNormUnits R S a) =
      affineDivisorPushforward R S (affinePrincipalDivisor (FractionRing S) a) := by
  obtain ⟨b, c, hc, hr⟩ := IsFractionRing.div_surjective (A := S) (a : FractionRing S)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb : b ≠ 0 := by
    intro hz
    apply a.ne_zero
    simp [hz] at hr
    exact hr.symm
  let u : (FractionRing S)ˣ := Units.mk0 (algebraMap S (FractionRing S) b)
    (by simpa using (IsFractionRing.injective S (FractionRing S)).ne hb)
  let v : (FractionRing S)ˣ := Units.mk0 (algebraMap S (FractionRing S) c)
    (by simpa using (IsFractionRing.injective S (FractionRing S)).ne hc0)
  have ha : a = u * v⁻¹ := by
    apply Units.ext
    simpa [u, v, div_eq_mul_inv] using hr.symm
  rw [ha, map_mul, map_inv, affinePrincipalDivisor_mul,
    affinePrincipalDivisor_inv, affinePrincipalDivisor_mul,
    affinePrincipalDivisor_inv, map_add, map_neg]
  dsimp [u, v]
  rw [separable_integral_principal_norm R S b hb,
    separable_integral_principal_norm R S c hc0]

/-- Actual affine-curve pushforward preserves the ground-field weighted
degree, proved from the tower law for residue-field degrees. -/
theorem affineDivisorPushforward_degree (k R S : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S] [Module.Finite R S]
    (D : HeightOneSpectrum S →₀ ℤ) :
    affineDivisorDegree k R (affineDivisorPushforward R S D) = affineDivisorDegree k S D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, hD, hE]
  | single q n =>
    rw [affineDivisorPushforward_single, affineDivisorDegree_single, affineDivisorDegree_single]
    have : q.asIdeal.LiesOver (q.under R).asIdeal := ⟨rfl⟩
    have h := Ideal.inertiaDeg_tower (R := k) (q.under R).asIdeal q.asIdeal
    rw [h, Nat.cast_mul]
    ring

/-- Degree of the divisor of a norm equals degree of the original
principal divisor on the actual affine Dedekind curves. No perfection
assumption on their fraction fields. Completion still needs infinity/gluing. -/
theorem separable_affine_principal_norm_degree (k R S : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (a : (FractionRing S)ˣ) :
    affineDivisorDegree k R (affinePrincipalDivisor (FractionRing R) (fractionFieldNormUnits R S a)) =
      affineDivisorDegree k S (affinePrincipalDivisor (FractionRing S) a) := by
  rw [separable_affine_principal_norm, affineDivisorPushforward_degree]

/-- Transfer separability to canonical fraction rings. The commuting
square is supplied by the genuine fraction-ring equivalences. -/
theorem fractionRing_separable_of_fractionFields (R S K L : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing R) (FractionRing S) := by
  apply Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv R K).symm.toRingEquiv
    (FractionRing.algEquiv S L).symm.toRingEquiv
  ext x
  exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv S L).symm x

/-- Norm as a map of nonzero rational functions on arbitrary chosen
function fields, not only the implementation's canonical fractions. -/
noncomputable def functionFieldNormUnits (K L : Type*) [Field K] [Field L]
    [Algebra K L] : Lˣ →* Kˣ := Units.map (Algebra.norm K : L →* K)

theorem separable_integral_functionField_norm (R S K L : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (a : S) (ha : a ≠ 0) :
    affinePrincipalDivisor K (functionFieldNormUnits K L
      (Units.mk0 (algebraMap S L a) (by simpa only [map_zero] using (IsFractionRing.injective S L).ne ha))) =
      affineDivisorPushforward R S (affinePrincipalDivisor L
        (Units.mk0 (algebraMap S L a) (by simpa only [map_zero] using (IsFractionRing.injective S L).ne ha))) := by
  let : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    fractionRing_separable_of_fractionFields R S K L
  let : FiniteDimensional K L := Module.Finite.of_isLocalization R S R⁰
  let : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have hn : functionFieldNormUnits K L
      (Units.mk0 (algebraMap S L a) (by simpa only [map_zero] using (IsFractionRing.injective S L).ne ha)) =
      Units.mk0 (algebraMap R K (Algebra.intNorm R S a))
        (by simpa only [map_zero] using (IsFractionRing.injective R K).ne (Algebra.intNorm_ne_zero.mpr ha)) := by
    apply Units.ext
    exact (Algebra.algebraMap_intNorm (K := K) (L := L) a).symm
  rw [hn]
  have h := separable_ideal_norm_divisor R S (Ideal.span {a}) (by simpa using ha)
  simpa only [Ideal.relNorm_singleton,
    idealFactorDivisor_principal R K _ (Algebra.intNorm_ne_zero.mpr ha),
    idealFactorDivisor_principal S L a ha] using h

/-- The actual principal norm formula, on arbitrary compatible chosen
function fields. No norm/divisor compatibility is an assumed input. -/
theorem separable_functionField_principal_norm (R S K L : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (a : Lˣ) :
    affinePrincipalDivisor K (functionFieldNormUnits K L a) =
      affineDivisorPushforward R S (affinePrincipalDivisor L a) := by
  obtain ⟨b, c, hc, hr⟩ := IsFractionRing.div_surjective (A := S) (a : L)
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hb : b ≠ 0 := by
    intro hz
    apply a.ne_zero
    simp [hz] at hr
    exact hr.symm
  let u : Lˣ := Units.mk0 (algebraMap S L b)
    (by simpa only [map_zero] using (IsFractionRing.injective S L).ne hb)
  let v : Lˣ := Units.mk0 (algebraMap S L c)
    (by simpa only [map_zero] using (IsFractionRing.injective S L).ne hc0)
  have ha : a = u * v⁻¹ := by
    apply Units.ext
    simpa [u, v, div_eq_mul_inv] using hr.symm
  rw [ha, map_mul, map_inv, affinePrincipalDivisor_mul,
    affinePrincipalDivisor_inv, affinePrincipalDivisor_mul,
    affinePrincipalDivisor_inv, map_add, map_neg]
  dsimp [u, v]
  rw [separable_integral_functionField_norm R S K L b hb,
    separable_integral_functionField_norm R S K L c hc0]

theorem separable_functionField_principal_norm_degree (k R S K L : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Algebra.IsSeparable K L]
    (a : Lˣ) :
    affineDivisorDegree k R (affinePrincipalDivisor K (functionFieldNormUnits K L a)) =
      affineDivisorDegree k S (affinePrincipalDivisor L a) := by
  rw [separable_functionField_principal_norm R S K L, affineDivisorPushforward_degree]

end Negativity
