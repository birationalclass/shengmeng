module
public import Linear.HomogeneousQuotient
public import Linear.HomogeneousPullbackComponents
public import Mathlib.LinearAlgebra.Dimension.Finrank
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K]

/-- The actual degree-m piece of the polynomial coordinate quotient. -/
def homogeneousQuotientPiece (I : Ideal (MvPolynomial σ K)) (m : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ K m).map (Ideal.Quotient.mkₐ K I).toLinearMap

theorem homogeneousQuotientPiece_mem_iff
    (I : Ideal (MvPolynomial σ K)) (m : ℕ) (a : MvPolynomial σ K ⧸ I) :
    a ∈ homogeneousQuotientPiece I m ↔
      ∃ H : MvPolynomial σ K, H.IsHomogeneous m ∧ Ideal.Quotient.mk I H = a := by
  rfl

theorem homogeneousQuotientPiece_finite [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (m : ℕ) :
    Module.Finite K (homogeneousQuotientPiece I m) := by
  exact Module.Finite.of_fg ((MvPolynomial.homogeneousSubmodule_fg σ K m).map _)

/-- The Hilbert function uses the actual finite-dimensional pieces, not a
supplied growth polynomial or a geometric dimension. -/
def homogeneousQuotientHilbert (I : Ideal (MvPolynomial σ K)) (m : ℕ) : ℕ :=
  Module.finrank K (homogeneousQuotientPiece I m)

theorem homogeneousQuotientComponent_mem_piece
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (m : ℕ) (a : MvPolynomial σ K ⧸ I) :
    homogeneousQuotientComponent I hI m a ∈ homogeneousQuotientPiece I m := by
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨MvPolynomial.homogeneousComponent m H,
    MvPolynomial.homogeneousComponent_isHomogeneous m H, rfl⟩

theorem homogeneousQuotientComponent_on_piece
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (m k : ℕ) (a : MvPolynomial σ K ⧸ I) (ha : a ∈ homogeneousQuotientPiece I k) :
    homogeneousQuotientComponent I hI m a = if m = k then a else 0 := by
  obtain ⟨H, hH, rfl⟩ := (homogeneousQuotientPiece_mem_iff I k a).mp ha
  rw [homogeneousQuotientComponent_mk, MvPolynomial.homogeneousComponent_of_mem hH]
  split_ifs <;> simp

theorem homogeneousQuotientPiece_disjoint
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    {m k : ℕ} (hmk : m ≠ k) :
    Disjoint (homogeneousQuotientPiece I m) (homogeneousQuotientPiece I k) := by
  apply Submodule.disjoint_def.mpr
  intro a ha hb
  have hm := homogeneousQuotientComponent_on_piece I hI m m a ha
  have hk := homogeneousQuotientComponent_on_piece I hI m k a hb
  simpa [hmk] using hm.symm.trans hk

theorem homogeneousQuotientComponent_decomposition
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (a : MvPolynomial σ K ⧸ I) :
    ∃ N : ℕ, (∑ m ∈ Finset.range N, homogeneousQuotientComponent I hI m a) = a := by
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨H.totalDegree + 1, ?_⟩
  simp only [homogeneousQuotientComponent_mk, ← map_sum, MvPolynomial.sum_homogeneousComponent]

theorem homogeneousQuotientPiece_mul_mem
    (I : Ideal (MvPolynomial σ K)) (m k : ℕ)
    (a b : MvPolynomial σ K ⧸ I)
    (ha : a ∈ homogeneousQuotientPiece I m) (hb : b ∈ homogeneousQuotientPiece I k) :
    a * b ∈ homogeneousQuotientPiece I (m + k) := by
  obtain ⟨H, hH, rfl⟩ := (homogeneousQuotientPiece_mem_iff I m a).mp ha
  obtain ⟨G, hG, rfl⟩ := (homogeneousQuotientPiece_mem_iff I k b).mp hb
  apply (homogeneousQuotientPiece_mem_iff I (m+k) _).mpr
  exact ⟨H * G, hH.mul hG, map_mul (Ideal.Quotient.mk I) H G⟩

end LinearStudy
