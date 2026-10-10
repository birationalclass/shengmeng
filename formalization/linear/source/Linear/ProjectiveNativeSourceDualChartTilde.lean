module
public import Linear.NativeSourceSpecChartTilde
public import Linear.ProjectiveNativeDualChartSectionsBijective
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra coextensionGradedBaseModule
  nativeHomogeneousAwayModuleScalar LocalizedModule.moduleOfIsLocalization
variable {n r : ℕ}

/-- SAME original finite normalization dual, identified as an actual module sheaf on its Spec chart.
Both section bijectivity and quasicoherence are DERIVED from the original hypotheses. -/
def projectiveNormalization_native_source_dual_chart_tildeIso
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
      tilde (ModuleCat.of (CommRingCat.of
        (HomogeneousLocalization.Away 𝓑 (φ (MvPolynomial.X i))))
        (nativeGradedModuleAwayZero 𝓑 𝒟 (φ (MvPolynomial.X i)))) ≅
        (nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0).restrict
          (Proj.awayι 𝓑 (φ (MvPolynomial.X i)) ha (by decide)) := by
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
  let F := nativeProjectiveModuleSheaf 𝓑 𝒟 hD 0
  letI : F.IsFinitePresentation :=
    projectiveLinearNormalization_native_dual_isFinitePresentation V L hL hfinite
  letI : F.IsQuasicoherent := inferInstance
  dsimp only
  intro ha
  exact nativeSourceSpecChartTildeIso 𝓑 𝒟 hD (φ (MvPolynomial.X i)) ha
    (projectiveNormalization_native_dual_chart_sections_bijective V L hL hinj hfinite i ha)

end LinearStudy
