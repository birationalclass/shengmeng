module
public import Linear.GradedHilbertSerre
public import Linear.HomogeneousCoordinateGrading
public import Mathlib.RingTheory.MvPolynomial.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K] [Finite σ]

/-- Hilbert--Serre for the ORIGINAL homogeneous coordinate quotient.
Its generating set, grading and finite degree pieces are constructed from I. -/
theorem homogeneousQuotientHilbertSeries_rational (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    ∃ p : Polynomial ℤ,
      (1 - PowerSeries.X) ^ Nat.card σ * gradedHilbertSeries (homogeneousQuotientPiece I) =
        (p : PowerSeries ℤ) := by
  classical
  letI := Fintype.ofFinite σ
  let A := MvPolynomial σ K ⧸ I
  let q := Ideal.Quotient.mkₐ K I
  let s : Finset A := Finset.univ.image (fun i : σ => q (MvPolynomial.X i))
  let 𝒜 := homogeneousQuotientPiece I
  letI : GradedAlgebra 𝒜 := homogeneousQuotientGrading I hI
  letI : ∀ n, Module.Finite K (𝒜 n) := fun n => homogeneousQuotientPiece_finite I n
  have hgen : Algebra.adjoin K (s : Set A) = ⊤ := by
    calc
      Algebra.adjoin K (s : Set A) =
          Algebra.adjoin K (q '' Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
        congr 1
        ext a
        simp [s]
      _ = (Algebra.adjoin K (Set.range (MvPolynomial.X : σ → MvPolynomial σ K))).map q :=
        (q.map_adjoin _).symm
      _ = q.range := by rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
      _ = ⊤ := (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective K I)
  have hdegree : ∀ a ∈ s, a ∈ 𝒜 1 := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i, rfl⟩
  obtain ⟨p, hp⟩ := gradedHilbertSeries_rational 𝒜 𝒜 s hgen hdegree
  have hcard : s.card ≤ Nat.card σ := by
    simpa [s, Nat.card_eq_fintype_card] using
      (Finset.card_image_le (s := Finset.univ) (f := fun i : σ => q (MvPolynomial.X i)))
  refine ⟨(1 - Polynomial.X) ^ (Nat.card σ - s.card) * p, ?_⟩
  calc
    (1 - PowerSeries.X) ^ Nat.card σ * gradedHilbertSeries 𝒜 =
        (1 - PowerSeries.X) ^ (Nat.card σ - s.card) *
          ((1 - PowerSeries.X) ^ s.card * gradedHilbertSeries 𝒜) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hcard]
    _ = (1 - PowerSeries.X) ^ (Nat.card σ - s.card) * (p : PowerSeries ℤ) := by rw [hp]
    _ = (((1 - Polynomial.X) ^ (Nat.card σ - s.card) * p : Polynomial ℤ) : PowerSeries ℤ) := by simp

end LinearStudy
