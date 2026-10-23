module
public import Linear.NativeProjectiveKoszulTermInternalExtVanishing
public import Linear.HomogeneousCoordinateGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
variable {K σ : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual quotient coordinate variables generate the SAME original
homogeneous coordinate quotient algebra. -/
theorem homogeneousQuotientCoordinate_adjoin_eq_top (I : Ideal (MvPolynomial σ K)) :
    Algebra.adjoin K (Set.range (fun i : σ => Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ := by
  let φ := Ideal.Quotient.mkₐ K I
  calc
    Algebra.adjoin K (Set.range (fun i : σ => φ (MvPolynomial.X i))) =
        Algebra.adjoin K (φ '' Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
      congr 1
      exact Set.range_comp φ MvPolynomial.X
    _ = (Algebra.adjoin K (Set.range (MvPolynomial.X : σ → MvPolynomial σ K))).map φ :=
      (φ.map_adjoin _).symm
    _ = φ.range := by rw [MvPolynomial.adjoin_range_X,Algebra.map_top]
    _ = ⊤ := (AlgHom.range_eq_top φ).mpr (Ideal.Quotient.mkₐ_surjective K I)

/-- The SAME ACTUAL homogeneous coordinate quotient Koszul source terms
have positive INTERNAL SHEAF Ext zero,ALL integerk and ALL p,N.
Coordinate generation/cover is DERIVED,not a new original-Setup premise. -/
theorem homogeneousQuotientKoszulTermInternalExt_succ
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (r d p : ℕ) (k : ℤ)
    (N : letI := homogeneousQuotientGrading I hI
      (AlgebraicGeometry.Proj (homogeneousQuotientPiece I)).Modules) (q : ℕ) :
    letI := homogeneousQuotientGrading I hI
    IsZero (schemeModuleInternalExt
      (nativeProjectiveKoszulTerm (homogeneousQuotientPiece I) r d p k) N (q+1)) := by
  letI := homogeneousQuotientGrading I hI
  exact nativeProjectiveKoszulTermInternalExt_succ (homogeneousQuotientPiece I)
    (fun i : σ => Ideal.Quotient.mk I (MvPolynomial.X i))
    (fun i => ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X K i,rfl⟩)
    (homogeneousQuotientCoordinate_adjoin_eq_top I) r d p k N q

end LinearStudy
