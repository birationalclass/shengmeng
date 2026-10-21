module
public import Linear.NativeIndependentNormalizationActualHComparison
public import Linear.ProjectiveNormalizationGradedDual
public import Linear.HomogeneousQuotientBaseGrading
public import Linear.NativeRingIntegerDecomposition
public import Linear.NativeRingIntegerBaseGrade
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
/-- For ORIGINAL V and its ORIGINAL finite linear normalization,ALL integer
native twists and ALL positive degrees,the ambient ordered Cech homology
is isomorphic to actual H of original V. Original coordinates generate the
source;the projection coordinates are NOT assumed to generate the source.
No injectivity,CM,smoothness,desired H comparison,or duality is supplied. -/
def originalNormalization_actualOrderedCechHigherHIso {n r : ℕ}
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i,(L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (k : ℤ) (q : ℕ) :=
  let R := MvPolynomial (Fin (r+1)) ℂ
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let phi := projectiveLinearNormalizationMap V L
  letI : Algebra R S := phi.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun z => (phi.commutes z).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  let A := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
  letI : Module.Finite R S := hfinite
  let D := nativeProjectiveRingIntegerPiece B
  letI : DirectSum.Decomposition D := nativeProjectiveRingIntegerDecomposition B
  let hS := nativeProjectiveRingIntegerPiece_graded B
  let hR := nativeRingIntegerBaseGradeCompatibility A B
  let a : Fin (r+1) → R := MvPolynomial.X
  have ha : ∀ i,a i ∈ A 1 := MvPolynomial.isHomogeneous_X ℂ
  let c : ULift.{0} (Fin (n+1)) → S := fun i => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i.down)
  have hc : ∀ i,c i ∈ B 1 := fun i => ⟨MvPolynomial.X i.down,MvPolynomial.isHomogeneous_X ℂ i.down,rfl⟩
  have hgenC : Algebra.adjoin ℂ (Set.range c) = ⊤ := homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal
  nativeIndependentFiniteNormalization_actualHigherHIso A B D hR hS a ha c hc
    MvPolynomial.adjoin_range_X hgenC k q
end LinearStudy
