module

public import Negativity.LocalGeometry
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open IsDedekindDomain

/-- Actual local length / residue-field degree formula for finite flat algebras.
This is a verified mathlib theorem used in the local proof of curve projection. -/
theorem finite_flat_fiber_degree (R S : Type*) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R =
      Module.finrank R S :=
  Ideal.sum_ramification_inertia_eq_finrank p S

/-- The same actual prime-fiber computation with signed Cartier multiplicity n.
No projection/intersection equality is assumed. -/
theorem finite_flat_signed_point_degree (R S : Type*) [CommRing R] [IsDomain R]
    [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] [Fintype (p.primesOver S)] (n : ℤ) :
    ∑ q : p.primesOver S,
      (n * (q.1.ramificationIdx R : ℤ)) * (q.1.inertiaDeg R : ℤ) =
      n * (Module.finrank R S : ℤ) := by
  have h : (∑ q : p.primesOver S,
      (q.1.ramificationIdx R : ℤ) * (q.1.inertiaDeg R : ℤ)) =
      (Module.finrank R S : ℤ) := by
    exact_mod_cast finite_flat_fiber_degree R S p
  simpa only [mul_assoc, ← Finset.mul_sum] using congrArg (fun z : ℤ => n * z) h

/-- In the domain/fraction-field setup, the rank in the point formula equals
the actual degree of the function-field extension. -/
theorem finite_flat_fiber_functionField_degree (R S K L : Type*)
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    (p : Ideal R) [p.IsPrime] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R =
      Module.finrank K L := by
  rw [finite_flat_fiber_degree R S p, IsFractionRing.finrank_eq R K S L]

/-- Signed order of a nonzero rational function at a height-one prime of an
actual Dedekind domain, defined from mathlib's normalized adic valuation. -/
noncomputable def heightOneOrder {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) (a : Kˣ) : ℤ :=
  -WithZero.log (p.valuation K (a : K))

/-- Orders add under multiplication of rational functions. -/
theorem heightOneOrder_mul {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) (a b : Kˣ) :
    heightOneOrder K p (a * b) = heightOneOrder K p a + heightOneOrder K p b := by
  have ha : p.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  have hb : p.valuation K (b : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr b.ne_zero
  simp only [heightOneOrder, Units.val_mul, map_mul, WithZero.log_mul ha hb, neg_add_rev]
  omega

/-- Pulling a nonzero rational local equation through an actual extension
multiplies its order by the actual ramification index. -/
theorem heightOneOrder_pullback {R S K : Type*} (L : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.IsTorsionFree R S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L]
    (p : HeightOneSpectrum R) (q : HeightOneSpectrum S)
    [q.asIdeal.LiesOver p.asIdeal] (a : Kˣ) :
    heightOneOrder L q (Units.map (algebraMap K L : K →* L) a) =
      (q.asIdeal.ramificationIdx R : ℤ) * heightOneOrder K p a := by
  unfold heightOneOrder
  change -WithZero.log (q.valuation L (algebraMap K L (a : K))) = _
  rw [← HeightOneSpectrum.valuation_liesOver L p q, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

/-- The actual point of Spec S associated with a prime over a nonzero point
of Spec R. Its height-one condition follows from lying over and injectivity. -/
def heightOnePrimeAbove {R S : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    (p : HeightOneSpectrum R) (q : p.asIdeal.primesOver S) : HeightOneSpectrum S :=
  ⟨q.1, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot q.1⟩

/-- The local projection computation with actual orders and residue degrees,
for a finite flat map of affine Dedekind curves. In particular, the Cartier
order compatibility is proved from valuations rather than assumed. -/
theorem finite_flat_order_fiber_degree {R S K : Type*} (L : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Flat R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (p : HeightOneSpectrum R) [Fintype (p.asIdeal.primesOver S)] (a : Kˣ) :
    ∑ q : p.asIdeal.primesOver S,
      heightOneOrder L (heightOnePrimeAbove p q)
        (Units.map (algebraMap K L : K →* L) a) * (q.1.inertiaDeg R : ℤ) =
      heightOneOrder K p a * (Module.finrank K L : ℤ) := by
  have hq (q : p.asIdeal.primesOver S) :
      heightOneOrder L (heightOnePrimeAbove p q)
        (Units.map (algebraMap K L : K →* L) a) =
      (q.1.ramificationIdx R : ℤ) * heightOneOrder K p a := by
    have : (heightOnePrimeAbove p q).asIdeal.LiesOver p.asIdeal :=
      show q.1.LiesOver p.asIdeal from inferInstance
    exact heightOneOrder_pullback L p (heightOnePrimeAbove p q) a
  calc
    _ = ∑ q : p.asIdeal.primesOver S,
        (heightOneOrder K p a * (q.1.ramificationIdx R : ℤ)) *
          (q.1.inertiaDeg R : ℤ) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [hq]
      ring
    _ = _ := by
      rw [finite_flat_signed_point_degree R S p.asIdeal,
        ← IsFractionRing.finrank_eq R K S L]

end Negativity
