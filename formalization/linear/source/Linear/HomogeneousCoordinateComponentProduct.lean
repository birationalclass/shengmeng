module
public import Linear.HomogeneousCoordinateGrading
public import Linear.GradedModuleProjection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K]

/-- The quotient components agree with the projections of the actual
internal grading constructed from the original homogeneous ideal. -/
theorem homogeneousQuotientComponent_eq_gradedProjection
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) (k : ℕ) :
    letI := homogeneousQuotientGrading I hI
    homogeneousQuotientComponent I hI k =
      gradedModuleProjection (homogeneousQuotientPiece I) k := by
  letI := homogeneousQuotientGrading I hI
  apply LinearMap.ext
  intro a
  induction a using DirectSum.Decomposition.inductionOn (homogeneousQuotientPiece I) with
  | zero => simp
  | @homogeneous d a =>
      rw [homogeneousQuotientComponent_on_piece I hI k d a a.property,
        gradedModuleProjection_on_piece (homogeneousQuotientPiece I) k d a a.property]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Multiplication by an actual homogeneous coordinate function shifts
the components by its degree, including the vanishing below that degree. -/
theorem homogeneousQuotientComponent_mul_homogeneous
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (d k : ℕ) (a b : MvPolynomial σ K ⧸ I)
    (hb : b ∈ homogeneousQuotientPiece I d) :
    homogeneousQuotientComponent I hI k (a * b) =
      if d ≤ k then homogeneousQuotientComponent I hI (k - d) a * b else 0 := by
  letI := homogeneousQuotientGrading I hI
  rw [homogeneousQuotientComponent_eq_gradedProjection I hI k,
    homogeneousQuotientComponent_eq_gradedProjection I hI (k-d)]
  simpa only [smul_eq_mul, mul_comm] using
    gradedModuleProjection_smul_homogeneous (homogeneousQuotientPiece I)
      (homogeneousQuotientPiece I) d k b hb a

end LinearStudy
