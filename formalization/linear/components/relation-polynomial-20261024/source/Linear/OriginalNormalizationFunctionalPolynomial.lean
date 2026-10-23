module
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
  nativeFiniteNormalization_specifiedActualTopHomDualIso nativeCoextensionFixedPolynomialFunctionalStatement
/-- On ORIGINAL V,choose ONE actual graded embedding degree BEFORE ALL
nonzero ORIGINAL scalar-linear top-H functionals. The full exposed generic
proposition retains the SAME actual dual representative,its adjoint at1,
the ORIGINAL degree-m polynomial Q and the exact image/comparison values.
The polynomial-image rule is DISCHARGED from the constructed embedding.
No canonical identification,cut support,or full original4.2 is claimed. -/
theorem originalNormalization_exists_fixed_polynomial_of_top_functional_above
    {n : ℕ} (V : IntegralProjectiveEquations n) (q : ℕ)
    (L : Fin (q+2) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (lower : ℕ) :
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
  ∃ m : ℕ,lower ≤ m ∧ 0 < m ∧ ∃ e : C →ₗ[S] S,Function.Injective e ∧
    nativeCoextensionFixedPolynomialFunctionalStatement (K:=ℂ) (S:=S) (σ:=Fin (q+2)) (τ:=Fin (n+1)) B
      (Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal) V.ideal.toIdeal m e c hc hgenC q (Fintype.card_fin (q+2)) := by
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
  have himages : ∃ m : ℕ,lower ≤ m ∧ 0 < m ∧ ∃ e : C →ₗ[S] S,Function.Injective e ∧
      ∀ z : C,z ∈ coextensionGradedPiece A B 0 → z ≠ 0 →
        ∃ Q : CoordinateRing n,Q.IsHomogeneous m ∧ Q ∉ V.ideal.toIdeal ∧
          Ideal.Quotient.mk V.ideal.toIdeal Q=e z :=
    originalNormalizationDual_exists_fixed_polynomial_images_above (n:=n) (r:=q+1) V L hL hinj hfinite lower
  obtain ⟨m,hbound,hm,e,he,hpolynomial⟩ := himages
  refine ⟨m,hbound,hm,e,he,?_⟩
  exact nativeCoextensionFixedPolynomialFunctionalStatement_of_images (K:=ℂ) (S:=S) (σ:=Fin (q+2)) (τ:=Fin (n+1)) B
    (Ideal.Quotient.mkₐ ℂ V.ideal.toIdeal) V.ideal.toIdeal m e c hc hgenC q (Fintype.card_fin (q+2)) hpolynomial
end LinearStudy
