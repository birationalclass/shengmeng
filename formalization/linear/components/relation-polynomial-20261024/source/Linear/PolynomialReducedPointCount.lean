module
public import Linear.FiniteReducedAlgebraPoints
public import Mathlib.RingTheory.Nullstellensatz
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K σ : Type*} [Field K]

/-- The actual zero locus is equivalent to scalar-valued algebra maps of
the actual polynomial quotient, by polynomial evaluation and coordinates. -/
def polynomialZeroLocusPointEquiv (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial.zeroLocus K I ≃ ((MvPolynomial σ K ⧸ I) →ₐ[K] K) where
  toFun x := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x.1) x.2
  invFun φ := by
    let x : σ → K := fun i => φ (Ideal.Quotient.mk I (MvPolynomial.X i))
    refine ⟨x, ?_⟩
    have he : MvPolynomial.aeval x = φ.comp (Ideal.Quotient.mkₐ K I) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [x]
    intro p hp
    rw [he]
    change φ (Ideal.Quotient.mk I p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv φ := by
    apply AlgHom.ext
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    change MvPolynomial.aeval (fun i => φ (Ideal.Quotient.mk I (MvPolynomial.X i))) p =
      φ (Ideal.Quotient.mk I p)
    have he : MvPolynomial.aeval (fun i => φ (Ideal.Quotient.mk I (MvPolynomial.X i))) =
        φ.comp (Ideal.Quotient.mkₐ K I) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp
    exact AlgHom.congr_fun he p

/-- For a reduced finite-dimensional polynomial quotient, the number of
ACTUAL affine zeroes equals its vector-space dimension. No cardinality
formula is supplied as a hypothesis. -/
theorem polynomialZeroLocus_card_eq_finrank [IsAlgClosed K]
    (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (MvPolynomial σ K ⧸ I)] [IsReduced (MvPolynomial σ K ⧸ I)] :
    Nat.card (MvPolynomial.zeroLocus K I) = Module.finrank K (MvPolynomial σ K ⧸ I) := by
  exact (Nat.card_congr (polynomialZeroLocusPointEquiv I)).trans
    (finiteReducedAlgebra_finrank_eq_rationalPoint_card (K := K)
      (A := MvPolynomial σ K ⧸ I)).symm

end LinearStudy
