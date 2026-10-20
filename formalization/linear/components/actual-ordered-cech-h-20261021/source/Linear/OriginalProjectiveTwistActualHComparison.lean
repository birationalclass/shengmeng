module
public import Linear.NativeProjActualHComparison
public import Linear.HomogeneousQuotientBaseGrading
public import Linear.NativeProjectiveTwistFinitePresentation
public import Linear.Projective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
/-- For ORIGINAL V,ALL integer twists (including NEGATIVE),and ALL positive
cohomological degrees,construct actual ordered Cech/native-H additive iso.
The ONLY inputs are V,k,q. Original coordinate cover,Noetherianity,finite
presentation,QC and actual local H acyclicity are all DERIVED.
This does not prove canonical-dualizing identification,perfect duality,
signed standard connecting-map compatibility or original4.1/4.2/main. -/
def originalProjectiveTwist_actualOrderedCechHigherHIso {n : ℕ}
    (V : IntegralProjectiveEquations n) (k : ℤ) (q : ℕ) :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : V.ideal.toIdeal.IsPrime := V.prime
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  let G := nativeProjectiveRingIntegerPiece B
  let hG := nativeProjectiveRingIntegerPiece_graded B
  letI : DirectSum.Decomposition G := nativeProjectiveRingIntegerDecomposition B
  let a : ULift.{0} (Fin (n+1)) → CoordinateRing n ⧸ V.ideal.toIdeal :=
    fun i => Ideal.Quotient.mk V.ideal.toIdeal (MvPolynomial.X i.down)
  have ha : ∀ i,a i ∈ B 1 :=
    fun i => ⟨MvPolynomial.X i.down,MvPolynomial.isHomogeneous_X ℂ i.down,rfl⟩
  have hgen : Algebra.adjoin ℂ (Set.range a) = ⊤ :=
    homogeneousQuotient_coordinate_adjoin_eq_top V.ideal.toIdeal
  have hcover : (⨆ i,Proj.basicOpen B (a i)) = ⊤ :=
    degreeOneGenerated_nativeProj_cover B a ha hgen
  let F := nativeProjectiveModuleSheaf B G hG k
  letI : F.IsFinitePresentation := nativeFiniteGradedTwist_isFinitePresentation_of_cover B G hG k a ha hcover
  letI : F.IsQuasicoherent := inferInstance
  finiteTypeNativeProj_orderedActualHigherHIso B a ha hcover F q
end LinearStudy
