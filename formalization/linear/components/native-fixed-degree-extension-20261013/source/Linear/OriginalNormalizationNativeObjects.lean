module
public import Linear.ProjectiveNormalizationLocallyFreeEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule

/-- The ACTUAL original native positive twist, with its exact original
quotient grading. This is an object definition, not a verified duality claim. -/
def originalProjectiveNativeTwist {n : ℕ} (V : IntegralProjectiveEquations n) (N : ℕ) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules :=
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let B := homogeneousQuotientPiece V.ideal.toIdeal
  nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
    (nativeProjectiveRingIntegerPiece_graded B) (N : ℤ)

/-- The ACTUAL native associated sheaf of the original normalization dual.
Only the given original degree-one forms are needed to define this object.
No canonical identification, injection or nonzero section is a data field. -/
def originalNormalizationNativeDualSheaf {n r : ℕ} (V : IntegralProjectiveEquations n)
    (L : Fin (r+1) → CoordinateRing n) (hL : ∀ i, (L i).IsHomogeneous 1) :
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    (Proj (homogeneousQuotientPiece V.ideal.toIdeal)).Modules := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ
  let 𝓑 := homogeneousQuotientPiece V.ideal.toIdeal
  letI : SetLike.GradedSMul 𝒜 𝓑 := projectiveLinearNormalization_gradedSMul V L hL
  exact nativeProjectiveModuleSheaf 𝓑 (coextensionGradedPiece 𝒜 𝓑)
    (coextensionProjectiveGradeCompatibility 𝒜 𝓑) 0
end LinearStudy
