module
public import Linear.NilpotentEvaluationUnique
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.FiniteType
/-! Actual finite thickening from nilpotent coordinate bounds. No finiteness
assumption is supplied: polynomial truncation and integral generators prove it. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ] [Nonempty σ]

theorem powerSeries_nilpotent_quotient_polynomial_surjective
    (I : Ideal (MvPowerSeries σ R)) (b : σ → ℕ)
    (hb : ∀ i, (MvPowerSeries.X i : MvPowerSeries σ R) ^ b i ∈ I) :
    Function.Surjective (MvPolynomial.aeval (R := R)
      (fun i => Ideal.Quotient.mk I (MvPowerSeries.X i))) := by
  let q := Ideal.Quotient.mkₐ R I
  let incl : MvPolynomial σ R →ₐ[R] MvPowerSeries σ R :=
    { MvPolynomial.coeToMvPowerSeries.ringHom with
      commutes' := by
        intro r
        change ((MvPolynomial.C r : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.C r
        exact MvPolynomial.coe_C r }
  have he : MvPolynomial.aeval (R := R) (fun i => Ideal.Quotient.mk I (MvPowerSeries.X i)) =
      q.comp incl := by
    ext i
    simp [incl, q, MvPolynomial.coe_X]
  rw [he]
  intro x
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective x
  let p := MvPowerSeries.trunc' R (Finsupp.equivFunOnFinite.symm b) H
  refine ⟨p, ?_⟩
  have hpow : ∀ i, q (MvPowerSeries.X i) ^ b i = 0 := by
    intro i
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hb i)
  exact (powerSeries_map_eq_trunc_of_nilpotent q.toRingHom b hpow H).symm

theorem powerSeries_nilpotent_quotient_finite
    (I : Ideal (MvPowerSeries σ R)) (b : σ → ℕ)
    (hb : ∀ i, (MvPowerSeries.X i : MvPowerSeries σ R) ^ b i ∈ I) :
    Module.Finite R (MvPowerSeries σ R ⧸ I) := by
  let Q := MvPowerSeries σ R ⧸ I
  let a : σ → Q := fun i => Ideal.Quotient.mk I (MvPowerSeries.X i)
  have hs : Function.Surjective (MvPolynomial.aeval (R := R) a) :=
    powerSeries_nilpotent_quotient_polynomial_surjective I b hb
  have ht : Algebra.adjoin R (Set.range a) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top]
    exact hs
  have hi : ∀ x ∈ Set.range a, IsIntegral R x := by
    rintro x ⟨i, rfl⟩
    refine ⟨Polynomial.X ^ b i, Polynomial.monic_X.pow _, ?_⟩
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hb i)
  have hf := fg_adjoin_of_finite (Set.finite_range a) hi
  rw [ht] at hf
  exact Module.Finite.of_fg_top (by simpa using hf)

theorem powerSeries_coordinateIdeal_power_quotient_finite
    (I : Ideal (MvPowerSeries σ R)) (e : ℕ)
    (he : (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) ^ e ≤ I) :
    Module.Finite R (MvPowerSeries σ R ⧸ I) :=
  powerSeries_nilpotent_quotient_finite I (fun _ => e)
    (fun _i => he (Ideal.pow_mem_pow Ideal.mem_span_range_self e))

end LinearStudy
