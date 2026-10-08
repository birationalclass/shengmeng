module
public import Linear.HomogeneousCoordinatePieces
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type*} [Field K]

theorem homogeneousQuotientPieces_iSupIndep
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    iSupIndep (homogeneousQuotientPiece I) := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (homogeneousQuotientPiece I)).mpr
  intro s v hv hsum m hm
  have h := congrArg (homogeneousQuotientComponent I hI m) hsum
  simp only [map_sum, map_zero] at h
  have hterms : (∑ k ∈ s, homogeneousQuotientComponent I hI m (v k)) =
      ∑ k ∈ s, if m = k then v k else 0 :=
    Finset.sum_congr rfl (fun k hk => homogeneousQuotientComponent_on_piece I hI m k (v k) (hv k hk))
  rw [hterms] at h
  simpa [hm] using h

theorem homogeneousQuotientPieces_iSup_eq_top
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    (⨆ m, homogeneousQuotientPiece I m) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro a
  obtain ⟨N, h⟩ := homogeneousQuotientComponent_decomposition I hI a
  rw [← h]
  apply Submodule.sum_mem
  intro m hm
  exact Submodule.mem_iSup_of_mem m (homogeneousQuotientComponent_mem_piece I hI m a)

/-- A genuine mathlib internal grading of the ORIGINAL polynomial quotient,
constructed from its actual homogeneous ideal, rather than supplied as
additional data. -/
@[instance_reducible] def homogeneousQuotientGrading
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K)) :
    GradedAlgebra (homogeneousQuotientPiece I) where
  __ := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (homogeneousQuotientPieces_iSupIndep I hI)
    (homogeneousQuotientPieces_iSup_eq_top I hI)).chooseDecomposition
  one_mem := (homogeneousQuotientPiece_mem_iff I 0 1).mpr
    ⟨1, MvPolynomial.isHomogeneous_one σ K, map_one (Ideal.Quotient.mk I)⟩
  mul_mem := by
    intro m k a b ha hb
    exact homogeneousQuotientPiece_mul_mem I m k a b ha hb

end LinearStudy
