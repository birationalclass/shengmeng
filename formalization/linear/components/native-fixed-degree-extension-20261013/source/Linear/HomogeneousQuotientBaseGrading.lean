module
public import Linear.HomogeneousCoordinateGrading
public import Linear.NativeRingIntegerDecomposition
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
universe u
variable {K : Type u} [Field K] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The scalar action of the ORIGINAL polynomial ring on its ORIGINAL
quotient respects the constructed homogeneous pieces. -/
theorem homogeneousQuotientBaseGradedSMul
    (I : Ideal (MvPolynomial σ K)) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) (homogeneousQuotientPiece I) := by
  refine ⟨?_⟩
  intro i j x y hx hy
  change Ideal.Quotient.mk I x * y ∈ homogeneousQuotientPiece I (i+j)
  exact homogeneousQuotientPiece_mul_mem I i j (Ideal.Quotient.mk I x) y
    ((homogeneousQuotientPiece_mem_iff I i _).mpr ⟨x,hx,rfl⟩) hy

/-- The actual quotient-coordinate images generate the original quotient
over K. The lifted index universe does not change this range. -/
theorem homogeneousQuotient_coordinate_adjoin_eq_top
    (I : Ideal (MvPolynomial σ K)) :
    Algebra.adjoin K (Set.range (fun i : ULift.{u} σ =>
      Ideal.Quotient.mk I (MvPolynomial.X i.down))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ K I
  have hr : Set.range (fun i : ULift.{u} σ => q (MvPolynomial.X i.down)) =
      q '' Set.range (MvPolynomial.X : σ → MvPolynomial σ K) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨MvPolynomial.X i.down,⟨i.down,rfl⟩,rfl⟩
    · rintro ⟨p,⟨i,rfl⟩,rfl⟩
      exact ⟨ULift.up i,rfl⟩
  change Algebra.adjoin K (Set.range (fun i : ULift.{u} σ => q (MvPolynomial.X i.down))) = ⊤
  rw [hr,← q.map_adjoin,MvPolynomial.adjoin_range_X,Algebra.map_top]
  exact (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective K I)
end LinearStudy
