module
public import Linear.CoextensionGradedModule
public import Linear.ProjectiveFiniteDualFinite
public import Linear.HomogeneousCoordinateComponentProduct
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
open CategoryTheory
variable {n r : ℕ}

/-- The original degree-one normalization defines the ACTUAL graded
scalar action on the original homogeneous coordinate quotient. -/
theorem projectiveLinearNormalization_gradedSMul
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  refine ⟨?_⟩
  intro d j a b ha hb
  have haH : a.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d a).mp ha
  have hae : (MvPolynomial.aeval L a).IsHomogeneous d := by
    simpa only [one_mul] using haH.aeval L hL
  have hφ : φ a ∈ homogeneousQuotientPiece V.ideal.toIdeal d :=
    (homogeneousQuotientPiece_mem_iff _ _ _).mpr ⟨MvPolynomial.aeval L a,hae,rfl⟩
  exact homogeneousQuotientPiece_mul_mem V.ideal.toIdeal d j (φ a) b hφ hb

/-- Construct the integer grading of the ACTUAL native dual of the
original finite linear normalization. No graded dual is supplied as input. -/
theorem projectiveLinearNormalization_exists_gradedDual
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    Nonempty (DirectSum.Decomposition
      (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
        (homogeneousQuotientPiece V.ideal.toIdeal))) := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  letI : Module.Finite A B := hfinite
  letI : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  exact ⟨coextensionGradedDecomposition (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
    (homogeneousQuotientPiece V.ideal.toIdeal)⟩

end LinearStudy
