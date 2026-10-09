module
public import Linear.CoextensionHomogeneousGenerators
public import Linear.ProjectiveNormalizationGradedDual
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
open CategoryTheory
variable {n r : ℕ}

/-- Finite homogeneous generators of the actual native dual over the
original homogeneous coordinate ring. Its grading and finiteness are
deduced from the actual finite linear normalization. -/
theorem projectiveLinearNormalization_exists_homogeneousDual_generators
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) :
    let A := MvPolynomial (Fin (r+1)) ℂ
    let B := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveLinearNormalizationMap V L
    letI : Algebra A B := φ.toRingHom.toAlgebra
    letI : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
    letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    ∃ s : Finset D, Submodule.span B (s : Set D) = ⊤ ∧
      ∀ ell ∈ s, ∃ d : ℤ,
        ell ∈ coextensionGradedPiece (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
          (homogeneousQuotientPiece V.ideal.toIdeal) d := by
  let A := MvPolynomial (Fin (r+1)) ℂ
  let B := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveLinearNormalizationMap V L
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  let := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  let : Module.Finite A B := hfinite
  let : SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ)
      (homogeneousQuotientPiece V.ideal.toIdeal) := projectiveLinearNormalization_gradedSMul V L hL
  exact nativeCoextensionDual_exists_homogeneous_generators
    (MvPolynomial.homogeneousSubmodule (Fin (r+1)) ℂ) (homogeneousQuotientPiece V.ideal.toIdeal)

end LinearStudy
