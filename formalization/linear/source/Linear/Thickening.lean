module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.Tactic

/-! # Actual one-variable nilpotent thickenings

For every s, work in the actual quotient B[[X]]/(X^(s+1)). We compute the
annihilator of X and its nonzero generator without any pairing assumption.
This is a monomial special case of the Jacobian step, not the general relative
complete-intersection lemma or the geometric Linearity Theorem.
-/

@[expose] public section
noncomputable section
namespace LinearStudy

variable (B : Type*) [CommRing B] (s : ℕ)

def thickeningIdeal : Ideal (PowerSeries B) :=
  Ideal.span {(PowerSeries.X : PowerSeries B) ^ (s + 1)}

abbrev Thickening := PowerSeries B ⧸ thickeningIdeal B s

def thickeningMk : PowerSeries B →+* Thickening B s :=
  Ideal.Quotient.mk (thickeningIdeal B s)

def thickeningX : Thickening B s := thickeningMk B s PowerSeries.X

def thickeningTop : Thickening B s := thickeningMk B s (PowerSeries.X ^ s)

theorem thickeningMk_surjective : Function.Surjective (thickeningMk B s) :=
  Ideal.Quotient.mk_surjective

theorem thickeningMk_eq_zero_iff (P : PowerSeries B) :
    thickeningMk B s P = 0 ↔ PowerSeries.X ^ (s + 1) ∣ P := by
  exact (Ideal.Quotient.eq_zero_iff_mem).trans Ideal.mem_span_singleton

theorem thickeningX_pow : (thickeningX B s) ^ (s + 1) = 0 := by
  rw [thickeningX, ← map_pow, thickeningMk_eq_zero_iff]

theorem thickeningX_nilpotent : IsNilpotent (thickeningX B s) :=
  ⟨s + 1, thickeningX_pow B s⟩

theorem thickening_X_annihilation_iff (P : PowerSeries B) :
    thickeningX B s * thickeningMk B s P = 0 ↔ PowerSeries.X ^ s ∣ P := by
  rw [thickeningX, ← map_mul, thickeningMk_eq_zero_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, PowerSeries.X_mul_cancel ?_⟩
    calc
      PowerSeries.X * P = PowerSeries.X ^ (s + 1) * h := hh
      _ = PowerSeries.X * (PowerSeries.X ^ s * h) := by rw [pow_succ']; ring
  · rintro ⟨h, rfl⟩
    refine ⟨h, ?_⟩
    rw [pow_succ']
    ring

theorem thickening_X_annihilator :
    (Ideal.span {thickeningX B s}).annihilator = Ideal.span {thickeningTop B s} := by
  ext a
  obtain ⟨P, rfl⟩ := thickeningMk_surjective B s a
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_comm,
    thickening_X_annihilation_iff, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨thickeningMk B s h, by simp [thickeningTop, map_mul]⟩
  · rintro ⟨h, hh⟩
    obtain ⟨Q, rfl⟩ := thickeningMk_surjective B s h
    have hzero : thickeningMk B s (P - PowerSeries.X ^ s * Q) = 0 := by
      simpa only [map_sub, map_mul, thickeningTop, sub_eq_zero] using hh
    have hdiv := (thickeningMk_eq_zero_iff B s _).mp hzero
    have hdiv' : PowerSeries.X ^ s ∣ P - PowerSeries.X ^ s * Q :=
      dvd_trans (pow_dvd_pow _ (Nat.le_succ s)) hdiv
    have := dvd_add hdiv' (dvd_mul_right (PowerSeries.X ^ s) Q)
    simpa using this

theorem thickeningTop_nonzero [Nontrivial B] : thickeningTop B s ≠ 0 := by
  intro h
  have hdiv := (thickeningMk_eq_zero_iff B s _).mp h
  have hc := PowerSeries.X_pow_dvd_iff.mp hdiv s (Nat.lt_succ_self s)
  simp at hc

/-- The actual reduction map is induced by the constant coefficient. -/
def thickeningReduction : Thickening B s →+* B :=
  Ideal.Quotient.lift (thickeningIdeal B s) PowerSeries.constantCoeff (by
    intro P hP
    obtain ⟨Q, rfl⟩ := Ideal.mem_span_singleton.mp hP
    simp)

@[simp] theorem thickeningReduction_mk (P : PowerSeries B) :
    thickeningReduction B s (thickeningMk B s P) = PowerSeries.constantCoeff P := rfl

theorem thickeningReduction_surjective : Function.Surjective (thickeningReduction B s) := by
  intro b
  exact ⟨thickeningMk B s (PowerSeries.C b), by simp⟩

theorem thickeningReduction_kernel :
    RingHom.ker (thickeningReduction B s) = Ideal.span {thickeningX B s} := by
  ext a
  obtain ⟨P, rfl⟩ := thickeningMk_surjective B s a
  change thickeningReduction B s (thickeningMk B s P) = 0 ↔ _
  rw [thickeningReduction_mk, ← PowerSeries.X_dvd_iff, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨thickeningMk B s Q, by simp [thickeningX, map_mul]⟩
  · rintro ⟨a, ha⟩
    have hconst := congrArg (thickeningReduction B s) ha
    apply PowerSeries.X_dvd_iff.mpr
    simpa [map_mul, thickeningX] using hconst

theorem thickening_nilradical [IsReduced B] :
    nilradical (Thickening B s) = Ideal.span {thickeningX B s} := by
  rw [← thickeningReduction_kernel]
  apply le_antisymm
  · intro a ha
    change thickeningReduction B s a = 0
    exact IsReduced.eq_zero _ ((mem_nilradical.mp ha).map (thickeningReduction B s))
  · rw [thickeningReduction_kernel]
    apply Ideal.span_le.mpr
    rintro a rfl
    exact mem_nilradical.mpr (thickeningX_nilpotent B s)

theorem thickening_nilradical_annihilator [IsReduced B] :
    (nilradical (Thickening B s)).annihilator = Ideal.span {thickeningTop B s} := by
  rw [thickening_nilradical, thickening_X_annihilator]

/-- This is the derivative of the defining equation, not an assumed generator. -/
def thickeningJacobian : Thickening B s :=
  thickeningMk B s (PowerSeries.derivative (PowerSeries.X ^ (s + 1)))

theorem thickeningJacobian_eq :
    thickeningJacobian B s = (s + 1 : ℕ) * thickeningTop B s := by
  simp [thickeningJacobian, thickeningTop, map_mul]

theorem thickeningJacobian_unit_twist (u : PowerSeries B) :
    thickeningMk B s (PowerSeries.derivative (u * PowerSeries.X ^ (s + 1))) =
      thickeningMk B s u * thickeningJacobian B s := by
  have hx : thickeningMk B s PowerSeries.X ^ (s + 1) = 0 := thickeningX_pow B s
  simp [map_add, map_mul, map_pow, hx, thickeningJacobian]

theorem thickeningJacobian_span (hunit : IsUnit ((s + 1 : ℕ) : B)) :
    Ideal.span {thickeningJacobian B s} = Ideal.span {thickeningTop B s} := by
  rw [thickeningJacobian_eq]
  apply Ideal.span_singleton_mul_left_unit
  simpa using hunit.map (algebraMap B (Thickening B s))

theorem thickeningJacobian_annihilator [IsReduced B]
    (hunit : IsUnit ((s + 1 : ℕ) : B)) :
    (nilradical (Thickening B s)).annihilator = Ideal.span {thickeningJacobian B s} := by
  rw [thickening_nilradical_annihilator, thickeningJacobian_span B s hunit]

theorem thickeningJacobian_nonzero [Nontrivial B]
    (hunit : IsUnit ((s + 1 : ℕ) : B)) : thickeningJacobian B s ≠ 0 := by
  rw [thickeningJacobian_eq]
  have hu : IsUnit ((s + 1 : ℕ) : Thickening B s) := by
    simpa using hunit.map (algebraMap B (Thickening B s))
  obtain ⟨u, hu⟩ := hu
  rw [← hu]
  intro h
  apply thickeningTop_nonzero B s
  have hh := congrArg (fun a => (↑u⁻¹ : Thickening B s) * a) h
  simpa [← mul_assoc] using hh

theorem thickeningTop_mul_mk (P : PowerSeries B) :
    thickeningTop B s * thickeningMk B s P =
      thickeningMk B s (PowerSeries.C (PowerSeries.constantCoeff P)) * thickeningTop B s := by
  obtain ⟨Q, hQ⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (P - PowerSeries.C (PowerSeries.constantCoeff P)) = 0 by simp)
  have hz : thickeningMk B s
      (PowerSeries.X ^ s * (P - PowerSeries.C (PowerSeries.constantCoeff P))) = 0 := by
    rw [thickeningMk_eq_zero_iff]
    refine ⟨Q, ?_⟩
    rw [hQ, pow_succ]
    ring
  change thickeningMk B s (PowerSeries.X ^ s) * thickeningMk B s P =
    thickeningMk B s (PowerSeries.C (PowerSeries.constantCoeff P)) *
      thickeningMk B s (PowerSeries.X ^ s)
  simpa only [mul_sub, map_sub, map_mul, sub_eq_zero, mul_comm] using hz

theorem thickening_nilradical_scalar_generation [IsReduced B] (a : Thickening B s) :
    a ∈ (nilradical (Thickening B s)).annihilator ↔
      ∃ b : B, a = thickeningMk B s (PowerSeries.C b) * thickeningTop B s := by
  rw [thickening_nilradical_annihilator, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨P, rfl⟩ := thickeningMk_surjective B s a
    exact ⟨PowerSeries.constantCoeff P, thickeningTop_mul_mk B s P⟩
  · rintro ⟨b, rfl⟩
    exact ⟨thickeningMk B s (PowerSeries.C b), mul_comm _ _⟩

theorem thickeningTop_scalar_eq_zero_iff (b : B) :
    thickeningMk B s (PowerSeries.C b) * thickeningTop B s = 0 ↔ b = 0 := by
  rw [thickeningTop, ← map_mul]
  rw [thickeningMk_eq_zero_iff, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h
    simpa using h s (Nat.lt_succ_self s)
  · rintro rfl
    simp

theorem thickeningTop_scalars_injective :
    Function.Injective (fun b : B => thickeningMk B s (PowerSeries.C b) * thickeningTop B s) := by
  intro b c h
  apply sub_eq_zero.mp
  apply (thickeningTop_scalar_eq_zero_iff B s _).mp
  simpa only [map_sub, sub_mul, sub_eq_zero] using h

theorem thickening_nilradical_maximal {K : Type*} [Field K] (s : ℕ) :
    (nilradical (Thickening K s)).IsMaximal := by
  rw [thickening_nilradical, ← thickeningReduction_kernel]
  exact RingHom.ker_isMaximal_of_surjective (thickeningReduction K s)
    (thickeningReduction_surjective K s)

theorem thickening_closedFiber_artinian {K : Type*} [Field K] (s : ℕ) :
    IsArtinianRing (Thickening K s) := by
  let : (nilradical (Thickening K s)).IsMaximal := thickening_nilradical_maximal s
  let : Ring.KrullDimLE 0 (Thickening K s) :=
    Ring.KrullDimLE.of_isMaximal_nilradical _
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem thickening_closedFiber_jacobian {K : Type*} [Field K] [CharZero K] (s : ℕ) :
    IsArtinianRing (Thickening K s) ∧
    (nilradical (Thickening K s)).IsMaximal ∧
      (nilradical (Thickening K s)).annihilator = Ideal.span {thickeningJacobian K s} ∧
      thickeningJacobian K s ≠ 0 := by
  have hu : IsUnit ((s + 1 : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero s))
  exact ⟨thickening_closedFiber_artinian s, thickening_nilradical_maximal s,
    thickeningJacobian_annihilator K s hu, thickeningJacobian_nonzero K s hu⟩

end LinearStudy
