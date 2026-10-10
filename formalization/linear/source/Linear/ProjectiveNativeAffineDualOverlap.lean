module
public import Linear.NormalizationHomogeneousAffineDualOverlapLocalization
public import Linear.NormalizationHomogeneousOverlapInjective
public import Linear.ProjectiveNativeGlobalChartDualityViaGeneric
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra normalizationHomogeneousSourceChartAlgebra
  LocalizedModule.moduleOfIsLocalization
variable {n r : ℕ}
/-- For the SAME original V and finite injective linear normalization, the
finite affine-dual comparison on the actual degree-two coordinate overlap
is constructed. Its base-overlap injectivity is DERIVED, not an input. This
still does not assert genuine global-Hom restriction compatibility. -/
def projectiveNormalization_affine_dual_overlap_linearEquiv
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i j : Fin (r+1)) :=
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
  normalizationHomogeneousAffineDualOverlapLinearEquiv 𝒜 𝓑
    (MvPolynomial.X i) (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X ℂ i) (MvPolynomial.isHomogeneous_X ℂ j)
    (projectiveCoordinateHomogeneousOverlap_injective r i j)
end LinearStudy
