module
public import Linear.NativeProjectiveChartSectionsInjective
public import Linear.ProjectiveNormalizationHomogeneousEmbedding
public import Linear.ProjectiveDualNativeFinitePresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
variable {n r : ℕ}

/-- Every original normalization coordinate separates actual native dual
chart elements as sections of the original source Proj. Torsion-freeness
is derived from the already constructed homogeneous dual embedding.
Neither it nor chart separation is an additional manuscript hypothesis.
This does not assert chart-section surjectivity or canonical identification. -/
theorem projectiveNormalization_native_dual_chart_sections_injective
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
    let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
    letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
    let 𝒟 := coextensionGradedPiece 𝒜 𝓑
    let hD := coextensionProjectiveGradeCompatibility 𝒜 𝓑
    ∀ ha : φ (MvPolynomial.X i) ∈ 𝓑 1,
      Function.Injective (nativeProjectiveChartDegreeZeroSectionMap 𝓑 𝒟 hD 1
        (φ (MvPolynomial.X i)) ha) := by
  letI := V.prime
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
  let D := (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)
  letI : IsScalarTower ℂ B D := IsScalarTower.of_compHom ℂ B D
  obtain ⟨m,hm,e,he,hhom⟩ :=
    projectiveLinearNormalization_exists_homogeneous_dual_embedding V L hL hinj hfinite
  letI : Module.IsTorsionFree B D :=
    he.moduleIsTorsionFree e (fun b d => e.map_smul b d)
  dsimp only
  intro ha
  apply nativeProjectiveChartDegreeZeroSectionMap_injective 𝓑
    (coextensionGradedPiece 𝒜 𝓑) (coextensionProjectiveGradeCompatibility 𝒜 𝓑)
    1 (by omega) (φ (MvPolynomial.X i)) ha
  intro hz
  apply MvPolynomial.X_ne_zero (R := ℂ) i
  apply hinj
  simpa only [map_zero] using hz

end LinearStudy
