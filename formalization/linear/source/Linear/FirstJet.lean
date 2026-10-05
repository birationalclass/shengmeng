module

public import Linear.DoublePoint
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.IntervalCases

/-!
# An actual power-series presentation of the double-point family

The first jet f ↦ coeff₀(f) + coeff₁(f) ε is a surjective B-algebra
homomorphism with kernel (X²). This identifies B[[X]]/(X²) with the explicit
square-zero extension and identifies its actual Jacobian with 2ε.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

variable (B : Type*) [CommRing B]

/-- The constant and linear coefficients, regarded as a square-zero element. -/
def firstJet : PowerSeries B →ₐ[B] DoublePoint B where
  toFun f := (PowerSeries.coeff 0 f, PowerSeries.coeff 1 f)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' f g := by
    ext
    · change PowerSeries.coeff 0 (f + g) = PowerSeries.coeff 0 f + PowerSeries.coeff 0 g
      simp
    · change PowerSeries.coeff 1 (f + g) = PowerSeries.coeff 1 f + PowerSeries.coeff 1 g
      simp
  map_mul' f g := by
    ext
    · change PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g
      simp
    · change PowerSeries.coeff 1 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
          PowerSeries.coeff 1 f * PowerSeries.coeff 0 g
      rw [PowerSeries.coeff_one_mul]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      ring
  commutes' b := by
    ext
    · change PowerSeries.coeff 0 (PowerSeries.C b) = b
      simp
    · change PowerSeries.coeff 1 (PowerSeries.C b) = 0
      simp

@[simp] theorem firstJet_fst (f : PowerSeries B) :
    (firstJet B f).fst = PowerSeries.coeff 0 f := rfl

@[simp] theorem firstJet_snd (f : PowerSeries B) :
    (firstJet B f).snd = PowerSeries.coeff 1 f := rfl

theorem firstJet_surjective : Function.Surjective (firstJet B) := by
  intro a
  refine ⟨PowerSeries.C a.fst + PowerSeries.C a.snd * PowerSeries.X, ?_⟩
  ext <;> simp

theorem firstJet_kernel :
    RingHom.ker (firstJet B) =
      Ideal.span {(PowerSeries.X : PowerSeries B) ^ 2} := by
  ext f
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  change firstJet B f = 0 ↔ _
  rw [TrivSqZeroExt.ext_iff]
  simp only [firstJet_fst, firstJet_snd, TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero]
  constructor
  · rintro ⟨h0, h1⟩ n hn
    interval_cases n <;> assumption
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide)⟩

/-- A genuine B-algebra isomorphism, with no presentation hypothesis. -/
def doublePointPowerSeriesEquiv :
    (PowerSeries B ⧸ Ideal.span {(PowerSeries.X : PowerSeries B) ^ 2}) ≃ₐ[B]
      DoublePoint B :=
  (Ideal.quotientEquivAlgOfEq B (firstJet_kernel B).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (firstJet_surjective B))

theorem doublePointPowerSeriesEquiv_mk (f : PowerSeries B) :
    doublePointPowerSeriesEquiv B (Ideal.Quotient.mk _ f) = firstJet B f := by
  change (Ideal.quotientKerAlgEquivOfSurjective (firstJet_surjective B))
    ((Ideal.quotientEquivAlgOfEq B (firstJet_kernel B).symm)
      (Ideal.Quotient.mk _ f)) = firstJet B f
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- Identify the actual derivative of the defining equation, not a chosen
annihilator element. -/
theorem doublePoint_actual_jacobian :
    firstJet B (PowerSeries.derivative ((PowerSeries.X : PowerSeries B) ^ 2)) =
      (2 : B) • epsilon B := by
  rw [PowerSeries.derivative_pow]
  ext
  · simp [epsilon, smul_eq_mul]
  · simp [epsilon, smul_eq_mul]
    exact map_ofNat (PowerSeries.constantCoeff (R := B)) 2

/-- Identify the actual Jacobian as a generator in the square-zero algebra,
with 2 invertible in the base. -/
theorem doublePoint_actual_jacobian_generates [IsReduced B]
    (h2 : IsUnit (2 : B)) (x : DoublePoint B) :
    Annihilates (nilradical (DoublePoint B)) x ↔
      ∃ b : B, x = b • firstJet B
        (PowerSeries.derivative ((PowerSeries.X : PowerSeries B) ^ 2)) := by
  rw [doublePoint_nilradical]
  have hd : Annihilates (RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom)
      (firstJet B (PowerSeries.derivative ((PowerSeries.X : PowerSeries B) ^ 2))) := by
    rw [doublePoint_actual_jacobian]
    have he := dualGenerator_annihilates (TrivSqZeroExt.fstHom B B B)
      (doublePointPerfectPairing B)
    rw [doublePoint_epsilon_is_dualGenerator] at he
    exact scalar_multiple_annihilates _ he 2
  apply unit_coefficient_generates_annihilator
    (TrivSqZeroExt.fstHom B B B) (doublePointPerfectPairing B) _ hd
  change IsUnit ((TrivSqZeroExt.sndHom B B)
    (firstJet B (PowerSeries.derivative ((PowerSeries.X : PowerSeries B) ^ 2))))
  rw [doublePoint_actual_jacobian]
  simpa [epsilon] using h2

/-- Annihilation of the nilradical is preserved by an actual algebra isomorphism. -/
theorem annihilates_nilradical_algEquiv
    {A C : Type*} [CommRing A] [CommRing C] [Algebra B A] [Algebra B C]
    (e : A ≃ₐ[B] C) (x : A) :
    Annihilates (nilradical A) x ↔ Annihilates (nilradical C) (e x) := by
  constructor
  · intro hx n hn
    have hn' : e.symm n ∈ nilradical A :=
      mem_nilradical.mpr ((mem_nilradical.mp hn).map e.symm)
    have h := congrArg e (hx (e.symm n) hn')
    simpa only [map_mul, map_zero, AlgEquiv.apply_symm_apply] using h
  · intro hx n hn
    apply e.injective
    rw [map_mul, map_zero]
    exact hx (e n) (mem_nilradical.mpr ((mem_nilradical.mp hn).map e))

/-- The first annihilator conclusion for the actual presentation B[[X]]/(X²).
Its generator is the class of the derivative of X². This is a proved family
of examples, not the universal Lemma31Goal for arbitrary regular sequences. -/
theorem quadratic_powerSeries_jacobian_annihilator [IsReduced B]
    (h2 : IsUnit (2 : B))
    (x : PowerSeries B ⧸ Ideal.span {(PowerSeries.X : PowerSeries B) ^ 2}) :
    Annihilates (nilradical
      (PowerSeries B ⧸ Ideal.span {(PowerSeries.X : PowerSeries B) ^ 2})) x ↔
      ∃ b : B, x = b • Ideal.Quotient.mk _
        (PowerSeries.derivative ((PowerSeries.X : PowerSeries B) ^ 2)) := by
  rw [annihilates_nilradical_algEquiv B (doublePointPowerSeriesEquiv B),
    doublePoint_actual_jacobian_generates B h2]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, (doublePointPowerSeriesEquiv B).injective ?_⟩
    rw [map_smul, doublePointPowerSeriesEquiv_mk]
    exact hb
  · rintro ⟨b, rfl⟩
    exact ⟨b, by rw [map_smul, doublePointPowerSeriesEquiv_mk]⟩

end LinearStudy
