module

public import Negativity.CurveDegree
public import Mathlib.RingTheory.TensorProduct.Quotient

@[expose] public section
namespace Negativity
open scoped TensorProduct

/-- Pulling back the closed subscheme of an ideal is extension of its ideal;
the quotient algebra is exactly base change by tensor product. -/
theorem point_pullback_tensor_iso (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) :
    Nonempty ((S ⧸ p.map (algebraMap R S)) ≃ₐ[S] S ⊗[R] (R ⧸ p)) :=
  ⟨Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p⟩

/-- At an actual point q over p, the tensor pullback has finite length equal
to the ramification multiplicity. Finiteness comes from quasi-finiteness and
Noetherianness, rather than being supplied as a numerical input. -/
theorem point_pullback_tensor_length {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Algebra.QuasiFinite R S]
    (p : Ideal R) (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Module.length (Localization.AtPrime q)
      ((Localization.AtPrime q) ⊗[R] (R ⧸ p)) = (q.ramificationIdx R : ℕ∞) := by
  let Sq := Localization.AtPrime q
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot Sq p
  have hfinite : Module.length Sq (Sq ⧸ p.map (algebraMap R Sq)) ≠ ⊤ := by
    rw [Module.length_eq_of_surjective
      (R := Sq ⧸ p.map (algebraMap R Sq)) Ideal.Quotient.mk_surjective]
    exact Module.length_ne_top
  rw [← e.toLinearEquiv.length_eq, Ideal.ramificationIdx_eq p q]
  exact (ENat.natCast_toNat hfinite).symm

/-- The point-divisor projection calculation: count tensor-pulled-back
points with their actual local lengths and relative residue-field weights. -/
theorem finite_flat_point_pullback_degree {R S K : Type*} (L : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (p : IsDedekindDomain.HeightOneSpectrum R) [Fintype (p.asIdeal.primesOver S)] :
    ∑ q : p.asIdeal.primesOver S,
      (Module.length (Localization.AtPrime q.1)
        ((Localization.AtPrime q.1) ⊗[R] (R ⧸ p.asIdeal))).toNat *
          q.1.inertiaDeg R = Module.finrank K L := by
  have hlength (q : p.asIdeal.primesOver S) := point_pullback_tensor_length p.asIdeal q.1
  simp_rw [hlength, ENat.toNat_natCast]
  exact finite_flat_fiber_functionField_degree R S K L p.asIdeal

/-- The same point-divisor calculation with degrees over the ground field:
Σ length_q(h*p) [k(q):k] = [L:K] [k(p):k]. This is the actual weighted
point count used for the degree of a divisor. -/
theorem finite_flat_point_pullback_degree_over_base {R S K : Type*} (k L : Type*)
    [Field k] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    [Module.Finite R S] [Module.Flat R S]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    (p : IsDedekindDomain.HeightOneSpectrum R) [Fintype (p.asIdeal.primesOver S)] :
    ∑ q : p.asIdeal.primesOver S,
      (Module.length (Localization.AtPrime q.1)
        ((Localization.AtPrime q.1) ⊗[R] (R ⧸ p.asIdeal))).toNat *
          q.1.inertiaDeg k = Module.finrank K L * p.asIdeal.inertiaDeg k := by
  calc
    _ = ∑ q : p.asIdeal.primesOver S,
        ((Module.length (Localization.AtPrime q.1)
          ((Localization.AtPrime q.1) ⊗[R] (R ⧸ p.asIdeal))).toNat *
            q.1.inertiaDeg R) * p.asIdeal.inertiaDeg k := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Ideal.inertiaDeg_tower p.asIdeal q.1]
      ring
    _ = _ := by
      rw [← Finset.sum_mul, finite_flat_point_pullback_degree (K := K) L p]

end Negativity
