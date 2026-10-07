module
public import Linear.NilpotentEvaluationUnique
public import Mathlib.RingTheory.Ideal.Quotient.Operations
/-! Actual reduced quotient of a coordinate-ideal thickening, constructed
from the constant-coefficient map and a power-ideal sandwich. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {R σ : Type*} [CommRing R] [IsDomain R]
  [Fintype σ] [DecidableEq σ] [Nonempty σ]

theorem powerSeries_thickening_radical
    (I : Ideal (MvPowerSeries σ R)) (e : ℕ) (he : 0 < e)
    (hupper : I ≤ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))))
    (hlower : (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) ^ e ≤ I) :
    I.radical = Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))) := by
  let J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hp : J.IsPrime := by
    dsimp only [J]
    rw [← powerSeries_constantCoeff_kernel]
    exact RingHom.ker_isPrime MvPowerSeries.constantCoeff
  apply le_antisymm
  · exact hp.radical_le_iff.mpr hupper
  · have h := Ideal.radical_mono hlower
    rw [Ideal.radical_pow _ (Nat.ne_zero_of_lt he), hp.isRadical.radical] at h
    exact h

def thickeningConstantCoeffAlgHom : MvPowerSeries σ R →ₐ[R] R :=
  { MvPowerSeries.constantCoeff with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

def powerSeriesThickeningReduction
    (I : Ideal (MvPowerSeries σ R))
    (hupper : I ≤ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) :
    (MvPowerSeries σ R ⧸ I) →ₐ[R] R :=
  Ideal.Quotient.liftₐ I thickeningConstantCoeffAlgHom
    (by
      change I ≤ RingHom.ker MvPowerSeries.constantCoeff
      rw [powerSeries_constantCoeff_kernel]
      exact hupper)

omit [IsDomain R] in
@[simp] theorem powerSeriesThickeningReduction_mk
    (I : Ideal (MvPowerSeries σ R))
    (hupper : I ≤ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))))
    (H : MvPowerSeries σ R) :
    powerSeriesThickeningReduction I hupper (Ideal.Quotient.mk I H) = H.constantCoeff := rfl

omit [IsDomain R] in
theorem powerSeriesThickeningReduction_surjective
    (I : Ideal (MvPowerSeries σ R))
    (hupper : I ≤ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) :
    Function.Surjective (powerSeriesThickeningReduction I hupper) := by
  intro r
  exact ⟨algebraMap R _ r, by simp⟩

omit [IsDomain R] in
theorem powerSeriesThickeningReduction_kernel
    (I : Ideal (MvPowerSeries σ R))
    (hupper : I ≤ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) :
    RingHom.ker (powerSeriesThickeningReduction I hupper).toRingHom =
      (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))).map
        (Ideal.Quotient.mk I) := by
  change RingHom.ker (Ideal.Quotient.lift I MvPowerSeries.constantCoeff _) = _
  rw [Ideal.ker_quotient_lift, powerSeries_constantCoeff_kernel]

theorem powerSeriesThickeningReduction_kernel_nilradical
    (I : Ideal (MvPowerSeries σ R)) (e : ℕ) (he : 0 < e)
    (hupper : I ≤ Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R))))
    (hlower : (Ideal.span (Set.range (MvPowerSeries.X (σ := σ) (R := R)))) ^ e ≤ I) :
    RingHom.ker (powerSeriesThickeningReduction I hupper).toRingHom =
      nilradical (MvPowerSeries σ R ⧸ I) := by
  rw [powerSeriesThickeningReduction_kernel,
    ← powerSeries_thickening_radical I e he hupper hlower]
  rw [Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker])]
  rw [Ideal.map_quotient_self]
  rfl

end LinearStudy
