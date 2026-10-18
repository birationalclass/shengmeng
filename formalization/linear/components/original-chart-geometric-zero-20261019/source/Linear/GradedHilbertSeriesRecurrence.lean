module
/-
The Hilbert--Serre generating-series identity, from the ACTUAL degreewise
multiplication maps and their exactness. No recurrence is supplied as data.
-/
public import Linear.GradedScalarExactSequence
public import Linear.GradedModuleFiniteSupport
public import Mathlib.RingTheory.PowerSeries.Trunc
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
variable [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M]
variable (𝒜 : ℕ → Submodule K A) [GradedAlgebra 𝒜]
variable (ℳ : ℕ → Submodule K M) [DirectSum.Decomposition ℳ]
variable [SetLike.GradedSMul 𝒜 ℳ]

/-- The actual homogeneous-piece dimensions, not an auxiliary numerical sequence. -/
def gradedHilbertSeries {P : Type*} [AddCommGroup P] [Module K P]
    (pieces : ℕ → Submodule K P) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (Module.finrank K (pieces n) : ℤ))

theorem gradedHilbertSeries_coeff (n : ℕ) :
    PowerSeries.coeff n (gradedHilbertSeries ℳ) = (Module.finrank K (ℳ n) : ℤ) :=
  PowerSeries.coeff_mk _ _

/-- The exact sequence gives the Hilbert--Serre series recurrence. -/
theorem gradedHilbertSeries_scalar_recurrence (d : ℕ) (x : A) (hx : x ∈ 𝒜 d)
    [∀ n, Module.Finite K (ℳ n)] :
    (1 - PowerSeries.X ^ d) * gradedHilbertSeries ℳ =
      gradedHilbertSeries
        (gradedQuotientPiece ℳ ((gradedScalarImage 𝒜 ℳ d x hx).toSubmodule.restrictScalars K)) -
      PowerSeries.X ^ d * gradedHilbertSeries
        (gradedSubmodulePiece ℳ ((gradedScalarKernel 𝒜 ℳ d x hx).toSubmodule.restrictScalars K)) := by
  apply PowerSeries.ext
  intro n
  rw [sub_mul, one_mul]
  simp only [map_sub, PowerSeries.coeff_X_pow_mul', gradedHilbertSeries, PowerSeries.coeff_mk]
  by_cases hdn : d ≤ n
  · simp only [if_pos hdn]
    have h := gradedScalar_finrank_recurrence 𝒜 ℳ d x hx (n - d)
    rw [Nat.add_sub_of_le hdn] at h
    have hi := congrArg (fun v : ℕ => (v : ℤ)) h
    push_cast at hi
    change (Module.finrank K (ℳ n) : ℤ) - Module.finrank K (ℳ (n - d)) =
      (Module.finrank K (gradedScalarCokernelPiece 𝒜 ℳ d x hx n) : ℤ) -
        Module.finrank K (gradedScalarKernelPiece 𝒜 ℳ d x hx (n - d))
    omega
  · simp only [if_neg hdn, sub_zero]
    have h := (gradedScalarCokernelPieceEquiv_of_lt 𝒜 ℳ d x hx n (Nat.lt_of_not_ge hdn)).finrank_eq
    exact_mod_cast h

/-- Bounded actual graded support gives a polynomial Hilbert series. -/
theorem gradedHilbertSeries_polynomial_of_bounded
    (h : ∃ N : ℕ, ∀ n : ℕ, N < n → ℳ n = ⊥) :
    ∃ p : Polynomial ℤ, (p : PowerSeries ℤ) = gradedHilbertSeries ℳ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨PowerSeries.trunc (N + 1) (gradedHilbertSeries ℳ), ?_⟩
  apply PowerSeries.ext
  intro n
  by_cases hn : n < N + 1
  · simp [PowerSeries.coeff_trunc, hn]
  · have hpiece : ℳ n = ⊥ := hN n (by omega)
    letI : Subsingleton (ℳ n) := by rw [hpiece]; infer_instance
    simp [PowerSeries.coeff_trunc, hn, gradedHilbertSeries,
      Module.finrank_zero_of_subsingleton]

/-- A finite total vector space has a polynomial Hilbert series. -/
theorem gradedHilbertSeries_polynomial_of_finite [Module.Finite K M] :
    ∃ p : Polynomial ℤ, (p : PowerSeries ℤ) = gradedHilbertSeries ℳ :=
  gradedHilbertSeries_polynomial_of_bounded ℳ (gradedModule_eventually_eq_bot ℳ)

theorem gradedHilbertSeries_polynomial_of_empty_generators [Module.Finite A M]
    (hgen : Algebra.adjoin K (∅ : Set A) = ⊤) :
    ∃ p : Polynomial ℤ, (p : PowerSeries ℤ) = gradedHilbertSeries ℳ :=
  gradedHilbertSeries_polynomial_of_bounded ℳ
    (gradedModule_eventually_eq_bot_of_empty_generators ℳ hgen)

end LinearStudy
