module
public import Linear.NativeNormalizationProjectiveMap
public import Linear.ProjectiveNormalizationGradedDual
public import Linear.NativeProjectiveDegreeOneCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n r : ℕ}

/-- The original linear forms now construct a morphism of actual native
projective schemes, without assuming a projective morphism or no-base-locus
certificate. It uses precisely the already proved finite cone map. -/
def projectiveLinearNormalizationSchemeMap
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Proj (homogeneousQuotientPiece V.ideal.toIdeal) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  letI : Module.Finite A B := hfinite
  exact nativeNormalizationProjectiveMap
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal)

/-- The same actual projective scheme morphism is finite. The standard
degree-one target charts cover because polynomial coordinates generate
the target algebra; their actual preimages are the original source charts. -/
theorem projectiveLinearNormalizationSchemeMap_isFinite
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    IsFinite (projectiveLinearNormalizationSchemeMap V L hL hfinite) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  letI : Module.Finite A B := hfinite
  apply nativeNormalizationProjectiveMap_isFinite_of_cover 𝒜 𝓑
    (MvPolynomial.X : Fin (r+1) → A) (MvPolynomial.isHomogeneous_X ℂ)
  exact degreeOneGenerated_nativeProj_cover 𝒜 MvPolynomial.X
    (MvPolynomial.isHomogeneous_X ℂ) MvPolynomial.adjoin_range_X

end LinearStudy
