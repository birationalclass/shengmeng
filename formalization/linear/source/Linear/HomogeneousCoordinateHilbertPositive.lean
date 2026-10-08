module
public import Linear.HomogeneousCoordinateHilbertPolynomial
public import Linear.Projective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K] [Finite σ]

/-- A surviving coordinate has a nonzero power in every actual homogeneous piece. -/
theorem homogeneousQuotientHilbert_pos_of_coordinate
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (j : σ)
    (hj : MvPolynomial.X j ∉ I) (m : ℕ) :
    0 < homogeneousQuotientHilbert I m := by
  let q := Ideal.Quotient.mk I
  have hq : q (MvPolynomial.X j) ≠ 0 := by
    intro h
    exact hj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hm : q (MvPolynomial.X j ^ m) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero m hq
  let a : homogeneousQuotientPiece I m :=
    ⟨q (MvPolynomial.X j ^ m), (homogeneousQuotientPiece_mem_iff I m _).mpr
      ⟨MvPolynomial.X j ^ m, by simpa using (MvPolynomial.isHomogeneous_X K j).pow m,
        rfl⟩⟩
  have ha : a ≠ 0 := by
    intro h
    exact hm (congrArg Subtype.val h)
  letI := homogeneousQuotientPiece_finite I m
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨a, ha⟩

/-- Nonemptiness of the ORIGINAL projective variety supplies a surviving coordinate. -/
theorem projective_coordinate_survives {n : ℕ} (V : IntegralProjectiveEquations n) :
    ∃ j : Fin (n + 1), MvPolynomial.X j ∉ V.ideal.toIdeal := by
  obtain ⟨v, hv, hvanish⟩ := V.nonempty
  have hj : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    funext j
    simpa using (not_exists.mp h j)
  obtain ⟨j, hj⟩ := hj
  refine ⟨j, fun h => hj ?_⟩
  simpa using hvanish (MvPolynomial.X j) h

/-- The ORIGINAL projective coordinate Hilbert function is positive in every degree. -/
theorem projective_coordinate_hilbert_pos {n : ℕ}
    (V : IntegralProjectiveEquations n) (m : ℕ) :
    0 < homogeneousQuotientHilbert V.ideal.toIdeal m := by
  letI := V.prime
  obtain ⟨j, hj⟩ := projective_coordinate_survives V
  exact homogeneousQuotientHilbert_pos_of_coordinate V.ideal.toIdeal j hj m

/-- The unique eventual Hilbert polynomial of the ORIGINAL nonempty integral
projective variety is nonzero and eventually positive. -/
theorem projective_coordinate_hilbertPolynomial_nonzero {n : ℕ}
    (V : IntegralProjectiveEquations n) :
    ∃ P : Polynomial ℚ, P ≠ 0 ∧ ∃ N : ℕ, ∀ m > N,
      P.eval (m : ℚ) = (homogeneousQuotientHilbert V.ideal.toIdeal m : ℚ) ∧
        0 < P.eval (m : ℚ) := by
  obtain ⟨P, ⟨N, hN⟩, _⟩ := homogeneousQuotientHilbertPolynomial_existsUnique
    V.ideal.toIdeal V.ideal.isHomogeneous
  have hpos (m : ℕ) (hm : m > N) : 0 < P.eval (m : ℚ) := by
    rw [hN m hm]
    exact_mod_cast projective_coordinate_hilbert_pos V m
  refine ⟨P, ?_, N, fun m hm => ⟨hN m hm, hpos m hm⟩⟩
  intro h
  have hp := hpos (N + 1) (by omega)
  simpa [h] using hp

end LinearStudy
