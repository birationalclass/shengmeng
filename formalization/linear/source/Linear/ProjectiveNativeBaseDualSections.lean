module
public import Linear.NativeCoextensionBaseSourceCharts
public import Linear.ProjectiveNativeDualChartSectionsBijective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeCoextensionNormalizationBaseModule
variable {n r : ℕ}

/-- The original base-localized finite dual chart is now bijective with
ACTUAL sections of the native dual sheaf on the original source Proj chart.
The comparison uses the proved universal base/source localization map and
the original chart section map. No chart equivalence or surjectivity is assumed. -/
theorem projectiveNormalization_native_base_dual_chart_sections_bijective
    (V : IntegralProjectiveEquations n) (L : Fin (r+1) → CoordinateRing n)
    (hL : ∀ i, (L i).IsHomogeneous 1)
    (hinj : Function.Injective (projectiveLinearNormalizationMap V L))
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (i : Fin (r+1)) :
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
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    ∀ ha : φ (MvPolynomial.X i) ∈ 𝓑 1,
      Function.Bijective (fun x : nativeGradedModuleAwayDegreeZero 𝒜 𝒟 1 (MvPolynomial.X i) =>
        nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1
          (φ (MvPolynomial.X i)) ha
          (nativeCoextensionBaseSourceChartEquiv 𝒜 𝓑 (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X ℂ i) x)) := by
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
  dsimp only
  intro ha
  exact (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i ha).comp
    (nativeCoextensionBaseSourceChartEquiv 𝒜 𝓑 (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i)).bijective
end LinearStudy
