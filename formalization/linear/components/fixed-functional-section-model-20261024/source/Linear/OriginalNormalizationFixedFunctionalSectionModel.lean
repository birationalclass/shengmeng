module
public import Linear.OriginalNormalizationPolynomialSectionEmbedding
public import Linear.OriginalPolynomialSectionImageProjections
public import Linear.OriginalNormalizationGradedPolynomial
public import Linear.NativeCoextensionFixedPolynomialFunctional
public import Linear.ProjectiveNormalizationGradedDual
public import Linear.HomogeneousQuotientBaseGrading
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  schemeModuleActualCohomologyAddCommGroup nativeProjectiveRingIntegerDecomposition
attribute [local irreducible] homogeneousQuotientGrading nativeProjectiveModuleSheaf
  nativeFiniteNormalization_specifiedActualTopHomDualIso nativeCoextensionFixedPolynomialFunctionalStatement originalGradedPolynomialSectionImageStatement

/-- FULL simultaneous fixed embedding/functional model;STATEMENT only. -/
def originalNormalizationFixedFunctionalSectionModelStatement
    {n : ℕ} (V : IntegralProjectiveEquations n) (q : ℕ)
    (L : Fin (q+2) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (lower : ℕ) : Prop :=
  let R := MvPolynomial (Fin (q+2)) ℂ
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let phi := projectiveLinearNormalizationMap V L
  letI : Algebra R S := phi.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun a => (phi.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  letI : Module.Finite R S := hfinite
  let A := MvPolynomial.homogeneousSubmodule (Fin (q+2)) ℂ
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
  let C := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let c : ULift.{0} (Fin (n+1)) → S := fun i => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i.down)
  have hc : ∀ i,c i ∈ B 1 := fun i => ⟨MvPolynomial.X i.down,MvPolynomial.isHomogeneous_X ℂ i.down,rfl⟩
  have hgenC : Algebra.adjoin ℂ (Set.range c) = ⊤ := homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal
  let DG := coextensionGradedPiece A B
  let EG := nativeProjectiveRingIntegerPiece B
  let hD := coextensionProjectiveGradeCompatibility A B
  let hE := nativeProjectiveRingIntegerPiece_graded B
  ∃ m : ℕ,lower ≤ m ∧ 0 < m ∧ ∃ e : C →ₗ[S] S,Function.Injective e ∧
    ∃ hh : ∀ d : ℤ,∀ z : C,z ∈ DG d → e z ∈ EG (d+(m:ℤ)),
    ∃ j : nativeProjectiveModuleSheaf B DG hD 0 ⟶ nativeProjectiveModuleSheaf B EG hE (m:ℤ),
      Mono j ∧ originalGradedPolynomialSectionImageStatement V DG hD m e j ∧
      nativeCoextensionFixedPolynomialFunctionalStatement (K:=ℂ) (S:=S) (σ:=Fin (q+2)) (τ:=Fin (n+1))
        B (Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal) V.ideal.toIdeal m e c hc hgenC q (Fintype.card_fin (q+2))
/-- ONE fixed original m/e/j simultaneously retains the FULL actual
section-image construction for ALL nonzero C_0 elements and the FULL
actual top-H functional polynomial witnesses with SAME e. No concrete
all-cut uniform assembly,canonical identity,or prescribed support claimed. -/
theorem originalNormalization_exists_fixed_functional_and_section_model_above
    {n : ℕ} (V : IntegralProjectiveEquations n) (q : ℕ)
    (L : Fin (q+2) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (lower : ℕ) :
    originalNormalizationFixedFunctionalSectionModelStatement V q L hL hfinite lower := by
  unfold originalNormalizationFixedFunctionalSectionModelStatement
  let R := MvPolynomial (Fin (q+2)) ℂ
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let phi := projectiveLinearNormalizationMap V L
  letI : Algebra R S := phi.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun a => (phi.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  letI : Module.Finite R S := hfinite
  let A := MvPolynomial.homogeneousSubmodule (Fin (q+2)) ℂ
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
  let C := (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R)
  let c : ULift.{0} (Fin (n+1)) → S := fun i => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i.down)
  have hc : ∀ i,c i ∈ B 1 := fun i => ⟨MvPolynomial.X i.down,MvPolynomial.isHomogeneous_X ℂ i.down,rfl⟩
  have hgenC : Algebra.adjoin ℂ (Set.range c) = ⊤ := homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal
  let DG := coextensionGradedPiece A B
  let EG := nativeProjectiveRingIntegerPiece B
  let hD := coextensionProjectiveGradeCompatibility A B
  let hE := nativeProjectiveRingIntegerPiece_graded B
  have hData : ∃ m : ℕ,lower ≤ m ∧ 0 < m ∧ ∃ e : C →ₗ[S] S,Function.Injective e ∧
      ∃ hh : ∀ d : ℤ,∀ z : C,z ∈ DG d → e z ∈ EG (d+(m:ℤ)),
      ∃ j : nativeProjectiveModuleSheaf B DG hD 0 ⟶ nativeProjectiveModuleSheaf B EG hE (m:ℤ),
        Mono j ∧ originalGradedPolynomialSectionImageStatement V DG hD m e j :=
    originalNormalizationDual_exists_polynomial_section_embedding_above
      (n:=n) (r:=q+1) V L hL hinj hfinite lower
  obtain ⟨m,hbound,hm,e,he,hh,j,hj,hImage⟩ := hData
  have himages : ∀ z : C,z ∈ coextensionGradedPiece A B 0 → z ≠ 0 →
      ∃ Q : CoordinateRing n,Q.IsHomogeneous m ∧ Q ∉ V.ideal.toIdeal ∧
        Ideal.Quotient.mk V.ideal.toIdeal Q=e z :=
    originalGradedPolynomialSectionImageStatement_polynomial_images
      (n:=n) (D:=C) V DG hD m e j hImage
  refine ⟨m,hbound,hm,e,he,hh,j,hj,hImage,?_⟩
  exact nativeCoextensionFixedPolynomialFunctionalStatement_of_images
    (K:=ℂ) (S:=S) (σ:=Fin (q+2)) (τ:=Fin (n+1)) B
      (Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal) V.ideal.toIdeal m e c hc hgenC q
        (Fintype.card_fin (q+2)) himages
end LinearStudy
