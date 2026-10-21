module
public import Linear.NativeFiniteNormalizationActualTopDuality
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
/-- Actual TOP sheaf H of ORIGINAL V under its given finite linear
normalization is the additive group of the dual of the ORIGINAL graded
Hom over that polynomial base. No finite presentation or desired pairing
is a premise. Canonical-dualizing identification and trace laws are OPEN. -/
def originalNormalization_actualTopHomDualIso {n : ℕ}
    (V : IntegralProjectiveEquations n) (q : ℕ)
    (L : Fin (q+2) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (k : ℤ) :=
  let R := MvPolynomial (Fin (q+2)) ℂ
  let S := CoordinateRing n ⧸ V.ideal.toIdeal
  let phi := projectiveLinearNormalizationMap V L
  letI : Algebra R S := phi.toRingHom.toAlgebra
  letI : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq (fun z => (phi.commutes z).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  let A := MvPolynomial.homogeneousSubmodule (Fin (q+2)) ℂ
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul A B := projectiveLinearNormalization_gradedSMul V L hL
  letI : Module.Finite R S := hfinite
  let D := nativeProjectiveRingIntegerPiece B
  letI : DirectSum.Decomposition D := nativeProjectiveRingIntegerDecomposition B
  let hS := nativeProjectiveRingIntegerPiece_graded B
  let hR := nativeRingIntegerBaseGradeCompatibility A B
  let c : ULift.{0} (Fin (n+1)) → S := fun i => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i.down)
  have hc : ∀ i,c i ∈ B 1 := fun i => ⟨MvPolynomial.X i.down,MvPolynomial.isHomogeneous_X ℂ i.down,rfl⟩
  have hgenC : Algebra.adjoin ℂ (Set.range c) = ⊤ := homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal
  nativeFiniteNormalization_actualTopHomDualIso (K := ℂ) (S := S) (M := S) (σ := Fin (q+2))
    B D hR hS c hc hgenC q (Fintype.card_fin (q+2)) k
end LinearStudy
