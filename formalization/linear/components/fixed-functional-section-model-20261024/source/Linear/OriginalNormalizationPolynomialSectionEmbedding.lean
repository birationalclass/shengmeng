module
public import Linear.OriginalNormalizationHomogeneousEmbeddingWitness
public import Linear.NativeHomogeneousEmbeddingSectionFormula
public import Linear.OriginalGradedPolynomialSectionImage
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveModuleSheaf originalGradedPolynomialSectionImageStatement
/-- Retain the SAME actual homogeneous embedding,its sheaf monomorphism,
and the exact image of EVERY degree-zero element as an ORIGINAL polynomial
section. ONE m precedes all elements. Nonzero of BOTH actual sections is
proved;canonical omega and prescribed local support remain OPEN. -/
theorem originalNormalizationDual_exists_polynomial_section_embedding_above
    {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (lower : ℕ) :
  let R := MvPolynomial (Fin (r+1)) ℂ
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let phi := projectiveLinearNormalizationMap V L
  letI : Algebra R S := phi.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun a => (phi.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let A := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
  let C := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let DG := coextensionGradedPiece A B
  let EG := nativeProjectiveRingIntegerPiece B
  let hD := coextensionProjectiveGradeCompatibility A B
  let hE := nativeProjectiveRingIntegerPiece_graded B
  ∃ m : ℕ,lower ≤ m ∧ 0 < m ∧ ∃ e : C →ₗ[S] S,Function.Injective e ∧
    ∃ hh : ∀ d : ℤ,∀ z : C,z ∈ DG d → e z ∈ EG (d+(m:ℤ)),
    ∃ j : nativeProjectiveModuleSheaf B DG hD 0 ⟶ nativeProjectiveModuleSheaf B EG hE (m:ℤ),
      Mono j ∧ originalGradedPolynomialSectionImageStatement V DG hD m e j := by
  let R := MvPolynomial (Fin (r+1)) ℂ
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let phi := projectiveLinearNormalizationMap V L
  letI : Algebra R S := phi.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun a => (phi.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let A := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
  let C := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let DG := coextensionGradedPiece A B
  let EG := nativeProjectiveRingIntegerPiece B
  let hD := coextensionProjectiveGradeCompatibility A B
  let hE := nativeProjectiveRingIntegerPiece_graded B
  have hEmbedding : ∃ m : ℕ,lower ≤ m ∧ 0 < m ∧
      ∃ e : C →ₗ[S] S,Function.Injective e ∧
      ∀ d : ℤ,∀ z : C,z ∈ DG d → e z ∈ EG (d+(m:ℤ)) :=
    originalNormalizationDual_exists_homogeneous_embedding_witness_above
      (n:=n) (r:=r) V L hL hinj hfinite lower
  obtain ⟨m,hbound,hm,e,he,hh⟩ := hEmbedding
  obtain ⟨j,hj,hformula⟩ :=
    nativeProjectiveHomogeneousInjection_exists_zero_degree_mono_sectionFormula
      (K:=ℂ) (S:=S) (D:=C) (E:=S) B DG EG hD hE (m:ℤ) e hh he
  refine ⟨m,hbound,hm,e,he,hh,j,hj,?_⟩
  exact originalGradedPolynomialSectionImageStatement_of_formula (n:=n) (D:=C) V DG hD m e j hj he hh hformula L hL hinj
end LinearStudy
