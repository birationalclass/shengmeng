module
public import Linear.NativeGlobalKoszulAffineCounit
public import Linear.HomogeneousCoordinateGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
variable {K σ : Type} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveKoszulOnAffine
  nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- The SAME ORIGINAL quotient coordinate classes generate its algebra;
this is derived from actual polynomial generators and the original quotient map. -/
theorem homogeneousQuotient_coordinate_adjoin_eq_top_unlifted (I : Ideal (MvPolynomial σ K)) :
    Algebra.adjoin K (Set.range (fun i : σ => Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ K I
  change Algebra.adjoin K (Set.range (fun i : σ => q (MvPolynomial.X i))) = ⊤
  calc
    Algebra.adjoin K (Set.range (fun i : σ => q (MvPolynomial.X i))) =
      Algebra.adjoin K (q '' Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
        congr 1
        exact Set.range_comp q MvPolynomial.X
    _ = (Algebra.adjoin K (Set.range (MvPolynomial.X : σ → MvPolynomial σ K))).map q :=
      (q.map_adjoin _).symm
    _ = q.range := by rw [MvPolynomial.adjoin_range_X, Algebra.map_top]
    _ = ⊤ := (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective K I)

/-- For the ORIGINAL finite homogeneous coordinate quotient,quasicoherence
of every actual global Koszul source term follows without assuming a grading,
Noetherianity,coordinate generation or source quasicoherence as extra data. -/
theorem homogeneousQuotientKoszulTerm_isQuasicoherent [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (r q p : ℕ) (k : ℤ) :
    letI := homogeneousQuotientGrading I hI
    (nativeProjectiveKoszulTerm (homogeneousQuotientPiece I) r q p k).IsQuasicoherent := by
  letI := homogeneousQuotientGrading I hI
  exact nativeProjectiveKoszulTerm_isQuasicoherent (homogeneousQuotientPiece I)
    (fun i : σ => Ideal.Quotient.mk I (MvPolynomial.X i))
    (fun i => ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X K i,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top_unlifted I) r q p k

/-- Apply the ACTUAL SHEAF-complex counit comparison to the SAME ORIGINAL
homogeneous coordinate quotient. Every source condition is DERIVED from the
original finite polynomial quotient;no assumption on a coefficient N is added.
The standard dehomogenized chart/scalar identification remains separate. -/
def homogeneousQuotientKoszulAffineCounitIso [Finite σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    {r q : ℕ} (H : Fin r → (MvPolynomial σ K ⧸ I)) (R : CommRingCat) (k : ℤ) :
    letI := homogeneousQuotientGrading I hI
    (hH : ∀ i, H i ∈ homogeneousQuotientPiece I q) →
    (j : Spec R ⟶ Proj (homogeneousQuotientPiece I)) → [IsOpenImmersion j] →
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (nativeProjectiveKoszulOnAffine (homogeneousQuotientPiece I) R j H hH k)) ≅
      nativeProjectiveKoszulOnAffine (homogeneousQuotientPiece I) R j H hH k := by
  letI := homogeneousQuotientGrading I hI
  intro hH j hj
  letI := hj
  exact nativeProjectiveKoszulAffineCounitIso (homogeneousQuotientPiece I)
    (fun i : σ => Ideal.Quotient.mk I (MvPolynomial.X i))
    (fun i => ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X K i,rfl⟩)
    (homogeneousQuotient_coordinate_adjoin_eq_top_unlifted I) R j H hH k

end LinearStudy
