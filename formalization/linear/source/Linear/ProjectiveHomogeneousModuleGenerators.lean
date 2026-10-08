module
public import Linear.GradedModuleHomogeneousGenerators
public import Linear.ProjectiveConeFinite
public import Linear.HomogeneousCoordinateFiltration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The ORIGINAL cone pullback has actual finite homogeneous module
generators. Its finite-module structure is derived from the no-base-point
homogeneous tuple, and the action is explicitly that original pullback. -/
theorem projectiveCoordinateDomainMap_exists_homogeneous_generators
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) :
    let A := CoordinateRing n ⧸ V.ideal.toIdeal
    let φ := projectiveCoordinateDomainMap f V hq hf hV
    letI : Algebra A A := φ.toRingHom.toAlgebra
    letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
    letI : Module A A := Algebra.toModule
    ∃ s : Finset A, Submodule.span A (s : Set A) = ⊤ ∧
      ∀ x ∈ s, ∃ d : ℕ, x ∈ homogeneousQuotientPiece V.ideal.toIdeal d := by
  let A := CoordinateRing n ⧸ V.ideal.toIdeal
  let φ := projectiveCoordinateDomainMap f V hq hf hV
  letI : Algebra A A := φ.toRingHom.toAlgebra
  letI : SMul A A := φ.toRingHom.toAlgebra.toSMul
  letI : Module A A := Algebra.toModule
  letI : Module.Finite A A := projectiveCoordinateDomainMap_finite f V hq hf hV
  letI := homogeneousQuotientGrading V.ideal.toIdeal V.ideal.isHomogeneous
  exact finiteModule_exists_homogeneous_generators (homogeneousQuotientPiece V.ideal.toIdeal)

end LinearStudy
