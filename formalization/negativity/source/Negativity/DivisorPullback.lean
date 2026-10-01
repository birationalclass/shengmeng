module

public import Negativity.PointPullback
public import Negativity.PrincipalDivisors
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Classical.propDecidable

noncomputable def affineDivisorDegree (k R : Type*) [Field k] [CommRing R]
    [IsDedekindDomain R] [Algebra k R] : (HeightOneSpectrum R →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun p => zmultiplesHom ℤ (p.asIdeal.inertiaDeg k : ℤ)

theorem affineDivisorDegree_single (k R : Type*) [Field k] [CommRing R]
    [IsDedekindDomain R] [Algebra k R] (p : HeightOneSpectrum R) (n : ℤ) :
    affineDivisorDegree k R (Finsupp.single p n) = n * (p.asIdeal.inertiaDeg k : ℤ) := by
  simp [affineDivisorDegree]

/-- Scheme-theoretic pullback of a point divisor on an affine normal curve.
The multiplicities are actual tensor-product lengths, not chosen weights. -/
noncomputable def affinePointDivisorPullback (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (p : HeightOneSpectrum R) : HeightOneSpectrum S →₀ ℤ :=
  ∑ q : p.asIdeal.primesOver S,
    Finsupp.single (heightOnePrimeAbove p q)
      ((Module.length (Localization.AtPrime q.1)
        ((Localization.AtPrime q.1) ⊗[R] (R ⧸ p.asIdeal))).toNat : ℤ)

/-- Extending genuine point pullbacks to arbitrary finite signed divisors. -/
noncomputable def affineDivisorPullback (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S] :
    (HeightOneSpectrum R →₀ ℤ) →+ (HeightOneSpectrum S →₀ ℤ) :=
  Finsupp.liftAddHom fun p => zmultiplesHom _ (affinePointDivisorPullback R S p)

/-- Weighted point count; flatness is derived from torsion-freeness over
the Dedekind domain, and no separability hypothesis is needed. -/
theorem affinePointDivisorPullback_degree (k R S K L : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] (p : HeightOneSpectrum R) :
    affineDivisorDegree k S (affinePointDivisorPullback R S p) =
      (Module.finrank K L : ℤ) * (p.asIdeal.inertiaDeg k : ℤ) := by
  classical
  unfold affinePointDivisorPullback
  rw [map_sum]
  simp_rw [affineDivisorDegree_single]
  exact_mod_cast finite_flat_point_pullback_degree_over_base (R := R) (S := S) (K := K) k L p

/-- The point formula extends by additivity to every finite signed divisor
on the actual affine Dedekind curve. This is a divisor degree computation,
not yet a definition of the degree of an arbitrary line bundle. -/
theorem affineDivisorPullback_degree (k R S K L : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] (D : HeightOneSpectrum R →₀ ℤ) :
    affineDivisorDegree k S (affineDivisorPullback R S D) =
      (Module.finrank K L : ℤ) * affineDivisorDegree k R D := by
  classical
  suffices (affineDivisorDegree k S).comp (affineDivisorPullback R S) =
      (zmultiplesHom ℤ (Module.finrank K L : ℤ)).comp (affineDivisorDegree k R) by
    simpa [mul_comm] using DFunLike.congr_fun this D
  apply Finsupp.addHom_ext
  intro p n
  simp only [AddMonoidHom.comp_apply, affineDivisorPullback,
    Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
  rw [map_zsmul, affinePointDivisorPullback_degree k R S K L p,
    affineDivisorDegree_single]
  simp only [zsmul_eq_mul, Int.cast_id]
  ring

/-- The coefficient of a pulled-back point is its actual tensor length if
the point lies above it, and zero otherwise. -/
theorem affinePointDivisorPullback_apply (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (p : HeightOneSpectrum R) (q : HeightOneSpectrum S) :
    affinePointDivisorPullback R S p q =
      if q.under R = p then (q.asIdeal.ramificationIdx R : ℤ) else 0 := by
  classical
  unfold affinePointDivisorPullback
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  by_cases h : q.under R = p
  · rw [ite_eq_left h]
    have : q.asIdeal.LiesOver p.asIdeal := by
      exact ⟨congrArg HeightOneSpectrum.asIdeal h.symm⟩
    let q' : p.asIdeal.primesOver S := ⟨q.asIdeal, inferInstance, inferInstance⟩
    have hq' : heightOnePrimeAbove p q' = q := HeightOneSpectrum.ext rfl
    rw [Finset.sum_eq_single q']
    · rw [ite_eq_left hq', point_pullback_tensor_length]
      simp [q', ENat.toNat_natCast]
    · intro t _ ht
      rw [ite_eq_right]
      intro he
      apply ht
      apply Subtype.ext
      exact congrArg HeightOneSpectrum.asIdeal he
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro t _
    rw [ite_eq_right]
    intro he
    apply h
    apply HeightOneSpectrum.ext
    have : t.1.LiesOver p.asIdeal := t.2.2
    have hu : t.1.under R = p.asIdeal := (Ideal.over_def t.1 p.asIdeal).symm
    change q.asIdeal.under R = p.asIdeal
    rw [← he]
    exact hu

/-- Pullback has the geometric coefficient e(q/p) times the coefficient
downstairs. This identifies tensor-length pullback with local orders. -/
theorem affineDivisorPullback_apply (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (D : HeightOneSpectrum R →₀ ℤ) (q : HeightOneSpectrum S) :
    affineDivisorPullback R S D q =
      (q.asIdeal.ramificationIdx R : ℤ) * D (q.under R) := by
  classical
  suffices (Finsupp.applyAddHom q).comp (affineDivisorPullback R S) =
      (zmultiplesHom ℤ (q.asIdeal.ramificationIdx R : ℤ)).comp
        (Finsupp.applyAddHom (q.under R)) by
    simpa [mul_comm] using DFunLike.congr_fun this D
  apply Finsupp.addHom_ext
  intro p n
  simp only [AddMonoidHom.comp_apply, affineDivisorPullback,
    Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]
  simp only [Finsupp.applyAddHom_apply, Finsupp.smul_apply,
    affinePointDivisorPullback_apply, Finsupp.single_apply]
  by_cases h : q.under R = p
  · simp [h]
  · simp [h, Ne.symm h]

/-- Pullback of actual principal divisors equals the divisor of the pulled
rational function. No divisor-compatibility identity is assumed. -/
theorem affinePrincipalDivisor_pullback (R S K L : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] (a : Kˣ) :
    affineDivisorPullback R S (affinePrincipalDivisor K a) =
      affinePrincipalDivisor L (Units.map (algebraMap K L : K →* L) a) := by
  ext q
  rw [affineDivisorPullback_apply, affinePrincipalDivisor_apply,
    affinePrincipalDivisor_apply]
  have : q.asIdeal.LiesOver (q.under R).asIdeal := ⟨rfl⟩
  exact (heightOneOrder_pullback L (q.under R) q a).symm

/-- Over an algebraically closed ground field, an actual closed point of a
finite-type affine curve has residue-field degree one (Zariski's lemma). -/
theorem closedPoint_residueDegree_one (k R : Type*)
    [Field k] [IsAlgClosed k] [CommRing R] [IsDedekindDomain R]
    [Algebra k R] [Algebra.FiniteType k R] (p : HeightOneSpectrum R) :
    p.asIdeal.inertiaDeg k = 1 := by
  let : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  let : Module.Finite k (R ⧸ p.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing k (R ⧸ p.asIdeal)
  let e : k ≃ₐ[k] (R ⧸ p.asIdeal) :=
    AlgEquiv.ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  rw [Ideal.inertiaDeg_eq_of_isMaximal (⊥ : Ideal k) p.asIdeal]
  have he : Module.finrank (k ⧸ (⊥ : Ideal k)) (R ⧸ p.asIdeal) =
      Module.finrank k (R ⧸ p.asIdeal) :=
    Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot k) (RingEquiv.refl _) (by
      ext x
      rfl)
  rw [he]
  simpa using e.toLinearEquiv.finrank_eq.symm

/-- In the user's arbitrary-characteristic algebraically closed setting,
the multiplicity count is unweighted: the sum of actual tensor lengths is
the full function-field degree, including inseparable degree. -/
theorem algebraicallyClosed_point_pullback_count (k R S K L : Type*)
    [Field k] [IsAlgClosed k]
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] (p : HeightOneSpectrum R) :
    ∑ q : p.asIdeal.primesOver S,
      (Module.length (Localization.AtPrime q.1)
        ((Localization.AtPrime q.1) ⊗[R] (R ⧸ p.asIdeal))).toNat =
      Module.finrank K L := by
  have h := finite_flat_point_pullback_degree_over_base (R := R) (S := S) (K := K) k L p
  have hq (q : p.asIdeal.primesOver S) : q.1.inertiaDeg k = 1 :=
    closedPoint_residueDegree_one k S (heightOnePrimeAbove p q)
  simpa only [hq, closedPoint_residueDegree_one k R p, mul_one] using h

/-- Actual finite curve pullback has precisely the inverse-image support. -/
theorem affineDivisorPullback_support (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (D : HeightOneSpectrum R →₀ ℤ) (q : HeightOneSpectrum S) :
    q ∈ (affineDivisorPullback R S D).support ↔ q.under R ∈ D.support := by
  rw [Finsupp.mem_support_iff, affineDivisorPullback_apply, Finsupp.mem_support_iff]
  have he : (q.asIdeal.ramificationIdx R : ℤ) ≠ 0 := by
    exact_mod_cast (q.asIdeal.ramificationIdx_pos R).ne'
  constructor
  · exact right_ne_zero_of_mul
  · exact mul_ne_zero he

/-- Effectivity of actual finite curve pullback is equivalent to effectivity
downstairs. Surjectivity of primes is proved by integral lying over. -/
theorem affineDivisorPullback_effective_iff (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (D : HeightOneSpectrum R →₀ ℤ) :
    (∀ q, 0 ≤ affineDivisorPullback R S D q) ↔ ∀ p, 0 ≤ D p := by
  have hlocal (q : HeightOneSpectrum S) :
      0 ≤ affineDivisorPullback R S D q ↔ 0 ≤ D (q.under R) := by
    rw [affineDivisorPullback_apply]
    have he : (0 : ℤ) < q.asIdeal.ramificationIdx R := by
      exact_mod_cast q.asIdeal.ramificationIdx_pos R
    exact mul_nonneg_iff_of_pos_left he
  constructor
  · intro h p
    obtain ⟨Q, hQ, hp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := S) p.asIdeal
    let q : HeightOneSpectrum S :=
      heightOnePrimeAbove p ⟨Q, hQ.isPrime, hp⟩
    have he : q.under R = p :=
      HeightOneSpectrum.ext (Ideal.over_def Q p.asIdeal).symm
    simpa only [he] using (hlocal q).mp (h q)
  · intro h q
    exact (hlocal q).mpr (h _)

/-- A nonzero effective finite divisor has strictly positive degree over an
algebraically closed field, with the actual residue-field degree weights. -/
theorem algebraicallyClosed_effective_divisor_degree_pos (k R : Type*)
    [Field k] [IsAlgClosed k] [CommRing R] [IsDedekindDomain R]
    [Algebra k R] [Algebra.FiniteType k R]
    (D : HeightOneSpectrum R →₀ ℤ) (hD : ∀ p, 0 ≤ D p) (hne : D ≠ 0) :
    0 < affineDivisorDegree k R D := by
  classical
  have hd : affineDivisorDegree k R D = ∑ p ∈ D.support, D p := by
    rw [affineDivisorDegree, Finsupp.liftAddHom_apply]
    change (∑ p ∈ D.support, (zmultiplesHom ℤ (p.asIdeal.inertiaDeg k : ℤ)) (D p)) = _
    simp [closedPoint_residueDegree_one]
  rw [hd]
  apply Finset.sum_pos'
  · intro p _
    exact hD p
  · obtain ⟨p, hp⟩ := Finsupp.support_nonempty_iff.mpr hne
    exact ⟨p, hp, lt_of_le_of_ne (hD p) (Finsupp.mem_support_iff.mp hp).symm⟩

end Negativity
