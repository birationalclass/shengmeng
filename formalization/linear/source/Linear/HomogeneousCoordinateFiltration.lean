module
public import Linear.HomogeneousCoordinateGrading
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K]

/-- The ORIGINAL coordinate quotient filtered by total degree at most N. -/
def homogeneousQuotientFiltration (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Submodule K (MvPolynomial σ K ⧸ I) := by
  classical
  exact (Finset.range (N + 1)).sup (homogeneousQuotientPiece I)

/-- The component filtration is exactly the image of actual bounded-degree
polynomials, not an arbitrary finite filtration supplied as input. -/
theorem homogeneousQuotientFiltration_eq_map
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    homogeneousQuotientFiltration I N =
      (MvPolynomial.restrictTotalDegree σ K N).map (Ideal.Quotient.mkₐ K I).toLinearMap := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro m hm a ha
    obtain ⟨H, hH, rfl⟩ := (homogeneousQuotientPiece_mem_iff I m a).mp ha
    refine ⟨H, (MvPolynomial.mem_restrictTotalDegree σ N H).mpr ?_, rfl⟩
    exact hH.totalDegree_le.trans (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  · rintro a ⟨H, hH, rfl⟩
    have hdeg := (MvPolynomial.mem_restrictTotalDegree σ N H).mp hH
    have he := congrArg (Ideal.Quotient.mk I) (MvPolynomial.sum_homogeneousComponent H)
    rw [map_sum] at he
    change (Ideal.Quotient.mk I) H ∈ homogeneousQuotientFiltration I N
    rw [← he]
    apply Submodule.sum_mem
    intro m hm
    have hmN : m ∈ Finset.range (N + 1) := by
      simp only [Finset.mem_range] at hm ⊢
      omega
    apply (Finset.le_sup (f := homogeneousQuotientPiece I) hmN)
    exact (homogeneousQuotientPiece_mem_iff I m _).mpr
      ⟨MvPolynomial.homogeneousComponent m H,
        MvPolynomial.homogeneousComponent_isHomogeneous m H, rfl⟩

theorem homogeneousQuotientFiltration_mem_iff
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) (a : MvPolynomial σ K ⧸ I) :
    a ∈ homogeneousQuotientFiltration I N ↔
      ∃ H : MvPolynomial σ K, H.totalDegree ≤ N ∧ Ideal.Quotient.mk I H = a := by
  rw [homogeneousQuotientFiltration_eq_map]
  simp only [Submodule.mem_map, MvPolynomial.mem_restrictTotalDegree]
  rfl

theorem homogeneousQuotientFiltration_finite [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Module.Finite K (homogeneousQuotientFiltration I N) := by
  rw [homogeneousQuotientFiltration_eq_map]
  infer_instance

theorem homogeneousQuotientFiltration_mono
    (I : Ideal (MvPolynomial σ K)) {N M : ℕ} (h : N ≤ M) :
    homogeneousQuotientFiltration I N ≤ homogeneousQuotientFiltration I M := by
  intro a ha
  obtain ⟨H, hH, he⟩ := (homogeneousQuotientFiltration_mem_iff I N a).mp ha
  exact (homogeneousQuotientFiltration_mem_iff I M a).mpr ⟨H, hH.trans h, he⟩

theorem homogeneousQuotientFiltration_succ
    (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    homogeneousQuotientFiltration I (N + 1) =
      homogeneousQuotientFiltration I N ⊔ homogeneousQuotientPiece I (N + 1) := by
  classical
  rw [homogeneousQuotientFiltration, Finset.range_add_one, Finset.sup_insert]
  unfold homogeneousQuotientFiltration
  ac_rfl

theorem homogeneousQuotientFiltration_disjoint_next
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) (N : ℕ) :
    Disjoint (homogeneousQuotientFiltration I N) (homogeneousQuotientPiece I (N + 1)) := by
  classical
  have h := (homogeneousQuotientPieces_iSupIndep I hI).disjoint_biSup
    (x := N + 1) (y := (↑(Finset.range (N + 1)) : Set ℕ)) (by simp)
  simpa [homogeneousQuotientFiltration, Finset.sup_eq_iSup] using h.symm

/-- The dimension of the actual bounded-degree quotient is the cumulative
Hilbert function, proved using independent homogeneous components. -/
theorem homogeneousQuotientFiltration_finrank [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) (N : ℕ) :
    Module.finrank K (homogeneousQuotientFiltration I N) =
      ∑ m ∈ Finset.range (N + 1), homogeneousQuotientHilbert I m := by
  classical
  induction N with
  | zero =>
      rw [homogeneousQuotientFiltration, Nat.zero_add, Finset.range_one, Finset.sup_singleton]
      simp [homogeneousQuotientHilbert]
  | succ N ih =>
      letI := homogeneousQuotientFiltration_finite I N
      letI := homogeneousQuotientPiece_finite I (N + 1)
      have h := Submodule.finrank_sup_add_finrank_inf_eq
        (homogeneousQuotientFiltration I N) (homogeneousQuotientPiece I (N + 1))
      rw [(homogeneousQuotientFiltration_disjoint_next I hI N).eq_bot,
        finrank_bot, add_zero] at h
      rw [homogeneousQuotientFiltration_succ, h, ih]
      conv_rhs => rw [Finset.sum_range_succ]
      rfl

end LinearStudy
